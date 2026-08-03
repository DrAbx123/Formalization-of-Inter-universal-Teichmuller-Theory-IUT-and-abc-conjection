/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceContinuousAnabelioid
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Open-subgroup slices of continuous-action anabelioids

Proposition 1.2.1(v) of Mochizuki's *The Geometry of Anabelioids*
identifies the slice of `B(G)` over the transitive object `G/H` with
`B(H)`.  Its inverse sends a finite continuous `H`-set `T` to the induced
`G`-set

`(G x T) / ((g, t) ~ (g h, h⁻¹ t))`.

This is the standard left-induction convention.  The paper instead takes the
left diagonal `H`-quotient and lets `G` act from the right by the inverse.  This
file constructs both conventions and the equivariant equivalence between them
before assembling the categorical equivalence.
-/

namespace Iut

universe u v w v'

open CategoryTheory
open CategoryTheory.Limits
open scoped FintypeCatDiscrete

/-! ## Open normal cores -/

/-- The normal core of an open subgroup of a profinite group, bundled with
its openness. -/
noncomputable def sourceOpenNormalCore
    (G : ProfiniteGrp.{u}) (K : Subgroup G) (hK : IsOpen (K : Set G)) :
    OpenNormalSubgroup G := by
  letI : Finite (G ⧸ K) :=
    K.quotient_finite_of_isOpen hK
  letI : Subgroup.FiniteIndex K :=
    K.finiteIndex_of_finite_quotient
  exact
    { toSubgroup := K.normalCore
      isOpen' :=
        Subgroup.isOpen_of_isClosed_of_finiteIndex _
          (K.normalCore_isClosed (K.isClosed_of_isOpen hK)) }

theorem sourceOpenNormalCore_le
    (G : ProfiniteGrp.{u}) (K : Subgroup G) (hK : IsOpen (K : Set G)) :
    (sourceOpenNormalCore G K hK).toSubgroup ≤ K :=
  K.normalCore_le

/-! ## The transitive object `G/H` -/

/-- The finite continuous left-coset action `G/H` associated to an open
subgroup `H` of a profinite group `G`. -/
noncomputable def sourceOpenCosetAction
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    ContAction FintypeCat.{u} G := by
  letI : Fintype (G ⧸ H.toSubgroup) :=
    Fintype.ofFinite _
  letI : TopologicalSpace (G ⧸ H.toSubgroup) := ⊥
  letI : DiscreteTopology (G ⧸ H.toSubgroup) := ⟨rfl⟩
  refine ⟨G ⧸ₐ H.toSubgroup, ?_⟩
  change ContinuousSMul G (G ⧸ H.toSubgroup)
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro q
  let N := sourceOpenNormalCore G H.toSubgroup H.isOpen
  apply Subgroup.isOpen_mono
    (H₁ := N.toSubgroup)
    (H₂ := MulAction.stabilizer G q) _ N.isOpen'
  intro n hn
  rw [MulAction.mem_stabilizer_iff]
  induction q using QuotientGroup.induction_on with
  | _ g =>
      rw [MulAction.Quotient.smul_mk]
      apply QuotientGroup.eq.mpr
      apply H.normalCore_le
      simpa only [smul_eq_mul, mul_inv_rev, inv_inv, mul_assoc,
        inv_mul_cancel_left] using
        H.toSubgroup.normalCore_normal.conj_mem
          n⁻¹ (H.toSubgroup.normalCore.inv_mem hn) g⁻¹

/-- The distinguished identity coset of `G/H`. -/
noncomputable def sourceOpenCosetBasepoint
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    (continuousActionFiber G).obj (sourceOpenCosetAction G H) := by
  change (sourceOpenCosetAction G H).obj.V
  exact QuotientGroup.mk (1 : G)

/-- The stabilizer of the distinguished point of `G/H` is literally `H`. -/
theorem sourceOpenCosetBasepoint_stabilizer
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    MulAction.stabilizer G (sourceOpenCosetBasepoint G H) = H.toSubgroup := by
  simp only [sourceOpenCosetBasepoint, sourceOpenCosetAction]
  exact MulAction.stabilizer_quotient H.toSubgroup

/-- Left translation sends the distinguished coset to the corresponding
coset. -/
theorem sourceOpenCoset_smul_basepoint
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) (g : G) :
    g • sourceOpenCosetBasepoint G H =
      (g : G ⧸ H.toSubgroup) := by
  simp only [sourceOpenCosetAction]
  change
    g • (QuotientGroup.mk (1 : G) :
      G ⧸ H.toSubgroup) = QuotientGroup.mk g
  rw [MulAction.Quotient.smul_mk]
  simp only [smul_eq_mul, mul_one]

/-! ## The induced set `(G x T)/H` -/

/-- The right-diagonal orbit relation for the standard left-induction
presentation of `(G x T)/H`. -/
def sourceInducedSetoid
    (G : Type u) [Group G] (H : Subgroup G)
    (T : Type u) [MulAction H T] :
    Setoid (G × T) where
  r a b :=
    ∃ h : H,
      b.1 = a.1 * (h : G) ∧
      b.2 = h⁻¹ • a.2
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨1, by simp, by simp⟩
    · rintro a b ⟨h, hb1, hb2⟩
      refine ⟨h⁻¹, ?_, ?_⟩
      · rw [hb1]
        simp
      · rw [hb2]
        simp
    · rintro a b c ⟨h, hb1, hb2⟩ ⟨k, hc1, hc2⟩
      refine ⟨h * k, ?_, ?_⟩
      · rw [hc1, hb1]
        simp only [Subgroup.coe_mul, mul_assoc]
      · rw [hc2, hb2]
        simp only [mul_inv_rev, mul_smul]

/-- The standard left-induction presentation of `(G x T)/H`. -/
abbrev SourceInducedSet
    (G : Type u) [Group G] (H : Subgroup G)
    (T : Type u) [MulAction H T] :=
  Quotient (sourceInducedSetoid G H T)

namespace SourceInducedSet

variable (G : Type u) [Group G] (H : Subgroup G)
variable (T : Type u) [MulAction H T]

/-- The class of `(g,t)` in `(G x T)/H`. -/
def mk (g : G) (t : T) : SourceInducedSet G H T :=
  Quotient.mk (sourceInducedSetoid G H T) (g, t)

theorem mk_eq_mk
    (g : G) (t : T) (h : H) :
    mk G H T (g * h) (h⁻¹ • t) = mk G H T g t := by
  exact
    (Quotient.sound
      (s := sourceInducedSetoid G H T)
      ⟨h, rfl, rfl⟩).symm

/-- Left translation on the first coordinate descends to the induced set. -/
instance : SMul G (SourceInducedSet G H T) where
  smul g :=
    Quotient.map
      (fun p : G × T => (g * p.1, p.2))
      (by
        rintro a b ⟨h, hb1, hb2⟩
        refine ⟨h, ?_, hb2⟩
        change g * b.1 = (g * a.1) * (h : G)
        rw [hb1]
        exact (mul_assoc g a.1 (h : G)).symm)

instance : MulAction G (SourceInducedSet G H T) where
  one_smul q := by
    induction q using Quotient.inductionOn with
    | _ p =>
        exact
          Quotient.sound
            (s := sourceInducedSetoid G H T)
            ⟨(1 : H), by simp, by simp⟩
  mul_smul g k q := by
    induction q using Quotient.inductionOn with
    | _ p =>
        exact
          Quotient.sound
            (s := sourceInducedSetoid G H T)
            ⟨(1 : H), by simp [mul_assoc], by simp⟩

@[simp]
theorem smul_mk (g k : G) (t : T) :
    g • mk G H T k t = mk G H T (g * k) t :=
  rfl

/-- A finite set of coset representatives times `T` surjects onto the induced
set.  This is the finiteness argument implicit in the source construction. -/
noncomputable def representativeMap
    [Finite (G ⧸ H)] :
    (G ⧸ H) × T → SourceInducedSet G H T :=
  fun p => mk G H T p.1.out p.2

theorem representativeMap_surjective
    [Finite (G ⧸ H)] :
    Function.Surjective (representativeMap G H T) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
      obtain ⟨h, hout⟩ :=
        QuotientGroup.mk_out_eq_mul H p.1
      refine
        ⟨((p.1 : G ⧸ H), h⁻¹ • p.2), ?_⟩
      exact
        (Quotient.sound
          (s := sourceInducedSetoid G H T)
          ⟨h, hout, rfl⟩).symm

noncomputable instance sourceInducedSet_finite
    [Finite (G ⧸ H)] [Finite T] :
    Finite (SourceInducedSet G H T) :=
  Finite.of_surjective
    (representativeMap G H T)
    (representativeMap_surjective G H T)

/-- The source projection `[g,t] |-> gH`. -/
def projection :
    SourceInducedSet G H T → G ⧸ H :=
  Quotient.lift
    (fun p : G × T => (p.1 : G ⧸ H))
    (by
      rintro a b ⟨h, hb1, _⟩
      change (a.1 : G ⧸ H) = (b.1 : G ⧸ H)
      rw [hb1]
      exact (QuotientGroup.mk_mul_of_mem a.1 h.property).symm)

@[simp]
theorem projection_mk (g : G) (t : T) :
    projection G H T (mk G H T g t) = (g : G ⧸ H) :=
  rfl

theorem projection_smul (g : G) (q : SourceInducedSet G H T) :
    projection G H T (g • q) = g • projection G H T q := by
  induction q using Quotient.inductionOn with
  | _ p => rfl

/-- An equivariant map of `H`-sets descends to a map of induced sets. -/
def map
    {U : Type u} [MulAction H U]
    (f : T → U)
    (equivariant : ∀ (h : H) (t : T), f (h • t) = h • f t) :
    SourceInducedSet G H T → SourceInducedSet G H U :=
  Quotient.map
    (fun p : G × T => (p.1, f p.2))
    (by
      rintro a b ⟨h, hb1, hb2⟩
      refine ⟨h, hb1, ?_⟩
      change f b.2 = h⁻¹ • f a.2
      rw [hb2]
      exact equivariant h⁻¹ a.2)

@[simp]
theorem map_mk
    {U : Type u} [MulAction H U]
    (f : T → U)
    (equivariant : ∀ (h : H) (t : T), f (h • t) = h • f t)
    (g : G) (t : T) :
    map G H T f equivariant (mk G H T g t) =
      mk G H U g (f t) :=
  rfl

theorem map_smul
    {U : Type u} [MulAction H U]
    (f : T → U)
    (equivariant : ∀ (h : H) (t : T), f (h • t) = h • f t)
    (g : G) (q : SourceInducedSet G H T) :
    map G H T f equivariant (g • q) =
      g • map G H T f equivariant q := by
  induction q using Quotient.inductionOn with
  | _ p => rfl

theorem projection_map
    {U : Type u} [MulAction H U]
    (f : T → U)
    (equivariant : ∀ (h : H) (t : T), f (h • t) = h • f t)
    (q : SourceInducedSet G H T) :
    projection G H U (map G H T f equivariant q) =
      projection G H T q := by
  induction q using Quotient.inductionOn with
  | _ p => rfl

end SourceInducedSet

/-! ## The paper's left-diagonal convention -/

/-- The orbit relation written in Proposition 1.2.1(v): `H` acts on
`G × T` by `h • (g,t) = (h g, h t)`. -/
def sourcePaperInducedSetoid
    (G : Type u) [Group G] (H : Subgroup G)
    (T : Type u) [MulAction H T] :
    Setoid (G × T) where
  r a b :=
    ∃ h : H,
      b.1 = (h : G) * a.1 ∧
      b.2 = h • a.2
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨1, by simp, by simp⟩
    · rintro a b ⟨h, hb1, hb2⟩
      refine ⟨h⁻¹, ?_, ?_⟩
      · rw [hb1]
        simp
      · rw [hb2]
        simp
    · rintro a b c ⟨h, hb1, hb2⟩ ⟨k, hc1, hc2⟩
      refine ⟨k * h, ?_, ?_⟩
      · rw [hc1, hb1]
        simp only [Subgroup.coe_mul, mul_assoc]
      · rw [hc2, hb2]
        exact (mul_smul k h a.2).symm

/-- The exact quotient set appearing in Proposition 1.2.1(v). -/
abbrev SourcePaperInducedSet
    (G : Type u) [Group G] (H : Subgroup G)
    (T : Type u) [MulAction H T] :=
  Quotient (sourcePaperInducedSetoid G H T)

namespace SourcePaperInducedSet

variable (G : Type u) [Group G] (H : Subgroup G)
variable (T : Type u) [MulAction H T]

/-- The class of `(g,t)` for the paper's left-diagonal quotient. -/
def mk (g : G) (t : T) : SourcePaperInducedSet G H T :=
  Quotient.mk (sourcePaperInducedSetoid G H T) (g, t)

/-- The paper's `G`-action: `k` acts on the first coordinate by right
multiplication by `k⁻¹`. -/
instance : SMul G (SourcePaperInducedSet G H T) where
  smul k :=
    Quotient.map
      (fun p : G × T => (p.1 * k⁻¹, p.2))
      (by
        rintro a b ⟨h, hb1, hb2⟩
        refine ⟨h, ?_, hb2⟩
        change b.1 * k⁻¹ = (h : G) * (a.1 * k⁻¹)
        rw [hb1, mul_assoc])

instance : MulAction G (SourcePaperInducedSet G H T) where
  one_smul q := by
    induction q using Quotient.inductionOn with
    | _ p =>
        change mk G H T (p.1 * (1 : G)⁻¹) p.2 =
          mk G H T p.1 p.2
        simp
  mul_smul g k q := by
    induction q using Quotient.inductionOn with
    | _ p =>
        change
          mk G H T (p.1 * (g * k)⁻¹) p.2 =
            mk G H T ((p.1 * k⁻¹) * g⁻¹) p.2
        simp only [mul_inv_rev, mul_assoc]

@[simp]
theorem smul_mk (k g : G) (t : T) :
    k • mk G H T g t = mk G H T (g * k⁻¹) t :=
  rfl

/-- Inversion of the first coordinate carries the paper's quotient to the
standard left-induction quotient. -/
def toStandard :
    SourcePaperInducedSet G H T → SourceInducedSet G H T :=
  Quotient.map
    (fun p : G × T => (p.1⁻¹, p.2))
    (by
      rintro a b ⟨h, hb1, hb2⟩
      refine ⟨h⁻¹, ?_, ?_⟩
      · change b.1⁻¹ = a.1⁻¹ * ((h⁻¹ : H) : G)
        rw [hb1]
        simp only [mul_inv_rev, Subgroup.coe_inv]
      · change b.2 = (h⁻¹ : H)⁻¹ • a.2
        simpa only [inv_inv] using hb2)

/-- Inversion of the first coordinate carries standard induction back to
the paper's quotient. -/
def fromStandard :
    SourceInducedSet G H T → SourcePaperInducedSet G H T :=
  Quotient.map
    (fun p : G × T => (p.1⁻¹, p.2))
    (by
      rintro a b ⟨h, hb1, hb2⟩
      refine ⟨h⁻¹, ?_, ?_⟩
      · change b.1⁻¹ = ((h⁻¹ : H) : G) * a.1⁻¹
        rw [hb1]
        simp only [mul_inv_rev, Subgroup.coe_inv]
      · exact hb2)

theorem fromStandard_toStandard
    (q : SourcePaperInducedSet G H T) :
    fromStandard G H T (toStandard G H T q) = q := by
  induction q using Quotient.inductionOn with
  | _ p =>
      change mk G H T (p.1⁻¹⁻¹) p.2 = mk G H T p.1 p.2
      rw [inv_inv]

theorem toStandard_fromStandard
    (q : SourceInducedSet G H T) :
    toStandard G H T (fromStandard G H T q) = q := by
  induction q using Quotient.inductionOn with
  | _ p =>
      change
        SourceInducedSet.mk G H T p.1⁻¹⁻¹ p.2 =
          SourceInducedSet.mk G H T p.1 p.2
      rw [inv_inv]

/-- The exact source convention and standard left induction are equivalent. -/
def equivStandard :
    SourcePaperInducedSet G H T ≃ SourceInducedSet G H T where
  toFun := toStandard G H T
  invFun := fromStandard G H T
  left_inv := fromStandard_toStandard G H T
  right_inv := toStandard_fromStandard G H T

/-- The inversion equivalence intertwines the paper's right-inverse action
with the standard left action. -/
theorem toStandard_smul
    (k : G) (q : SourcePaperInducedSet G H T) :
    toStandard G H T (k • q) = k • toStandard G H T q := by
  induction q using Quotient.inductionOn with
  | _ p =>
      change
        SourceInducedSet.mk G H T (p.1 * k⁻¹)⁻¹ p.2 =
          SourceInducedSet.mk G H T (k * p.1⁻¹) p.2
      rw [mul_inv_rev, inv_inv]

end SourcePaperInducedSet

/-! ## The induced continuous action -/

noncomputable instance sourcePaperInducedSet_finite
    {G : Type u} [Group G] (H : Subgroup G)
    (T : Type u) [MulAction H T]
    [Finite (G ⧸ H)] [Finite T] :
    Finite (SourcePaperInducedSet G H T) :=
  Finite.of_injective
    (SourcePaperInducedSet.toStandard G H T)
    (SourcePaperInducedSet.equivStandard G H T).injective

/-- The stabilizer of a point of a continuous `H`-action, mapped into `G`,
is open in `G` when `H` is open. -/
theorem sourceMappedStabilizer_isOpen
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H) (t : T.obj.V) :
    IsOpen
      ((MulAction.stabilizer H t).map H.toSubgroup.subtype :
        Set G) := by
  rw [Subgroup.coe_map]
  exact
    H.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _
      (by
        haveI : ContinuousSMul H T.obj.V := T.property
        exact stabilizer_isOpen H t)

/-- Every stabilizer in the induced set is open. This is the mathematical
continuity argument used for both quotient conventions. -/
theorem sourceInducedSet_stabilizer_isOpen
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (q : SourceInducedSet G H.toSubgroup T.obj.V) :
    IsOpen (MulAction.stabilizer G q : Set G) := by
  induction q using Quotient.inductionOn with
  | _ p =>
      let U : Subgroup H := MulAction.stabilizer H p.2
      let K : Subgroup G := U.map H.toSubgroup.subtype
      have hK_open : IsOpen (K : Set G) := by
        exact sourceMappedStabilizer_isOpen G H T p.2
      let N := sourceOpenNormalCore G K hK_open
      apply Subgroup.isOpen_mono
        (H₁ := N.toSubgroup)
        (H₂ :=
          MulAction.stabilizer G
            (SourceInducedSet.mk G H.toSubgroup T.obj.V p.1 p.2))
        _ N.isOpen'
      intro n hn
      rw [MulAction.mem_stabilizer_iff]
      rw [SourceInducedSet.smul_mk]
      have hconjN :
          p.1⁻¹ * n * p.1 ∈ N.toSubgroup := by
        simpa only [inv_inv] using
          (inferInstance : N.toSubgroup.Normal).conj_mem n hn p.1⁻¹
      have hconjK :
          p.1⁻¹ * n * p.1 ∈ K :=
        sourceOpenNormalCore_le G K hK_open hconjN
      change
        p.1⁻¹ * n * p.1 ∈
          (MulAction.stabilizer H p.2).map H.toSubgroup.subtype at hconjK
      obtain ⟨h, hh, h_eq⟩ :=
        Subgroup.mem_map.mp hconjK
      have hfix :
          h⁻¹ • p.2 = p.2 := by
        rw [← MulAction.mem_stabilizer_iff]
        exact (MulAction.stabilizer H p.2).inv_mem hh
      have hgroup :
          n * p.1 = p.1 * (h : G) := by
        have h_eq' :
            (h : G) = p.1⁻¹ * n * p.1 :=
          h_eq
        calc
          n * p.1 =
              p.1 * (p.1⁻¹ * n * p.1) := by group
          _ = p.1 * (h : G) :=
            congrArg (p.1 * ·) h_eq'.symm
      calc
        SourceInducedSet.mk G H.toSubgroup T.obj.V (n * p.1) p.2 =
            SourceInducedSet.mk G H.toSubgroup T.obj.V
              (p.1 * h) (h⁻¹ • p.2) := by
                rw [hfix, hgroup]
        _ =
            SourceInducedSet.mk G H.toSubgroup T.obj.V p.1 p.2 :=
          SourceInducedSet.mk_eq_mk G H.toSubgroup T.obj.V p.1 p.2 h

/-- The standard induced set `(G x T)/H`, equipped with its proved continuous
`G`-action. -/
noncomputable def sourceInducedAction
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H) :
    ContAction FintypeCat.{u} G := by
  letI : Finite (G ⧸ H.toSubgroup) :=
    H.toSubgroup.quotient_finite_of_isOpen H.isOpen
  letI : Fintype (SourceInducedSet G H.toSubgroup T.obj.V) :=
    Fintype.ofFinite _
  letI : TopologicalSpace (SourceInducedSet G H.toSubgroup T.obj.V) := ⊥
  letI : DiscreteTopology (SourceInducedSet G H.toSubgroup T.obj.V) := ⟨rfl⟩
  refine
    ⟨Action.FintypeCat.ofMulAction G
      (FintypeCat.of (SourceInducedSet G H.toSubgroup T.obj.V)), ?_⟩
  change ContinuousSMul G (SourceInducedSet G H.toSubgroup T.obj.V)
  rw [continuousSMul_iff_stabilizer_isOpen]
  exact sourceInducedSet_stabilizer_isOpen G H T

/-- The exact left-diagonal/right-inverse convention of Proposition 1.2.1(v),
packaged as a finite continuous `G`-action. -/
noncomputable def sourcePaperInducedAction
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H) :
    ContAction FintypeCat.{u} G := by
  letI : Finite (G ⧸ H.toSubgroup) :=
    H.toSubgroup.quotient_finite_of_isOpen H.isOpen
  letI : Fintype (SourcePaperInducedSet G H.toSubgroup T.obj.V) :=
    Fintype.ofFinite _
  letI : TopologicalSpace
      (SourcePaperInducedSet G H.toSubgroup T.obj.V) := ⊥
  letI : DiscreteTopology
      (SourcePaperInducedSet G H.toSubgroup T.obj.V) := ⟨rfl⟩
  refine
    ⟨Action.FintypeCat.ofMulAction G
      (FintypeCat.of
        (SourcePaperInducedSet G H.toSubgroup T.obj.V)), ?_⟩
  change ContinuousSMul G
    (SourcePaperInducedSet G H.toSubgroup T.obj.V)
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro q
  let K :=
    MulAction.stabilizer G
      (SourcePaperInducedSet.toStandard
        G H.toSubgroup T.obj.V q)
  have hK_open : IsOpen (K : Set G) :=
    sourceInducedSet_stabilizer_isOpen G H T
      (SourcePaperInducedSet.toStandard
        G H.toSubgroup T.obj.V q)
  apply Subgroup.isOpen_mono
    (H₁ := K)
    (H₂ := MulAction.stabilizer G q) _ hK_open
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  apply (SourcePaperInducedSet.equivStandard
    G H.toSubgroup T.obj.V).injective
  change
    SourcePaperInducedSet.toStandard
        G H.toSubgroup T.obj.V (g • q) =
      SourcePaperInducedSet.toStandard
        G H.toSubgroup T.obj.V q
  rw [SourcePaperInducedSet.toStandard_smul, hg]

/-- The paper-convention induced action is isomorphic, in `B(G)`, to the
standard induced action used in the slice equivalence. -/
noncomputable def sourcePaperInducedActionIso
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H) :
    sourcePaperInducedAction G H T ≅ sourceInducedAction G H T := by
  dsimp only [sourcePaperInducedAction, sourceInducedAction]
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ ?_
  · change
      FintypeCat.of
          (SourcePaperInducedSet G H.toSubgroup T.obj.V) ≅
        FintypeCat.of
          (SourceInducedSet G H.toSubgroup T.obj.V)
    exact FintypeCat.equivEquivIso
      (SourcePaperInducedSet.equivStandard
        G H.toSubgroup T.obj.V)
  · intro g
    ext q
    exact SourcePaperInducedSet.toStandard_smul
      G H.toSubgroup T.obj.V g q

/-- The equivariant source projection from the induced `G`-action to
`G/H`. -/
noncomputable def sourceInducedActionProjection
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H) :
    sourceInducedAction G H T ⟶ sourceOpenCosetAction G H :=
  ObjectProperty.homMk
    ({ hom :=
        FintypeCat.homMk
          (SourceInducedSet.projection G H.toSubgroup T.obj.V)
       comm := fun g => by
         ext q
         exact SourceInducedSet.projection_smul
           G H.toSubgroup T.obj.V g q } :
      (sourceInducedAction G H T).obj ⟶
        (sourceOpenCosetAction G H).obj)

/-- The underlying function of a morphism of continuous actions is
equivariant. -/
theorem sourceContinuousActionMap_equivariant
    (H : Type u) [Group H] [TopologicalSpace H]
    {T U : ContAction FintypeCat.{u} H} (f : T ⟶ U)
    (h : H) (t : T.obj.V) :
    f.hom.hom (h • t) = h • f.hom.hom t := by
  have hcomm :=
    ConcreteCategory.congr_hom (f.hom.comm h) t
  exact hcomm

/-- Induction on morphisms of finite continuous `H`-actions. -/
noncomputable def sourceInducedActionMap
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    {T U : ContAction FintypeCat.{u} H} (f : T ⟶ U) :
    sourceInducedAction G H T ⟶ sourceInducedAction G H U :=
  ObjectProperty.homMk
    ({ hom :=
        FintypeCat.homMk
          (SourceInducedSet.map G H.toSubgroup T.obj.V
            f.hom.hom
            (sourceContinuousActionMap_equivariant H f))
       comm := fun g => by
         ext q
         change
           SourceInducedSet.map G H.toSubgroup T.obj.V f.hom.hom
               (sourceContinuousActionMap_equivariant H f) (g • q) =
             g • SourceInducedSet.map G H.toSubgroup T.obj.V f.hom.hom
               (sourceContinuousActionMap_equivariant H f) q
         exact SourceInducedSet.map_smul
           G H.toSubgroup T.obj.V f.hom.hom
             (sourceContinuousActionMap_equivariant H f) g q } :
      (sourceInducedAction G H T).obj ⟶
        (sourceInducedAction G H U).obj)

@[simp]
theorem sourceInducedActionMap_projection
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    {T U : ContAction FintypeCat.{u} H} (f : T ⟶ U) :
    sourceInducedActionMap G H f ≫ sourceInducedActionProjection G H U =
      sourceInducedActionProjection G H T := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext q
  change
    SourceInducedSet.projection G H.toSubgroup U.obj.V
        (SourceInducedSet.map G H.toSubgroup T.obj.V f.hom.hom
          (sourceContinuousActionMap_equivariant H f) q) =
      SourceInducedSet.projection G H.toSubgroup T.obj.V q
  exact SourceInducedSet.projection_map
    G H.toSubgroup T.obj.V f.hom.hom
      (sourceContinuousActionMap_equivariant H f) q

/-- The source induction functor `T |-> ((G x T)/H -> G/H)`. -/
noncomputable def sourceInductionToSlice
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    ContAction FintypeCat.{u} H ⥤ Over (sourceOpenCosetAction G H) where
  obj T := Over.mk (sourceInducedActionProjection G H T)
  map f :=
    Over.homMk (sourceInducedActionMap G H f)
      (sourceInducedActionMap_projection G H f)
  map_id T := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext q
    induction q using Quotient.inductionOn with
    | _ p => rfl
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext q
    induction q using Quotient.inductionOn with
    | _ p => rfl

/-! ## The fiber functor from the slice -/

/-- The literal fiber over the identity coset of an object `X -> G/H` in the
slice. -/
noncomputable def SourceOpenCosetSliceFiber
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (X : Over (sourceOpenCosetAction G H)) :=
  { x : X.left.obj.V //
    X.hom.hom.hom x = sourceOpenCosetBasepoint G H }

namespace SourceOpenCosetSliceFiber

variable (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
variable (X : Over (sourceOpenCosetAction G H))

noncomputable instance :
    Fintype (SourceOpenCosetSliceFiber G H X) := by
  letI : Fintype X.left.obj.V := FintypeCat.fintype
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The subgroup `H` acts on the fiber because it fixes the distinguished
coset. -/
noncomputable instance sourceOpenCosetSliceFiber_mulAction :
    MulAction H (SourceOpenCosetSliceFiber G H X) where
  smul h x :=
    ⟨(h : G) • x.val, by
      calc
        X.hom.hom.hom ((h : G) • x.val) =
            (h : G) • X.hom.hom.hom x.val := by
              exact ConcreteCategory.congr_hom
                (X.hom.hom.comm (h : G)) x.val
        _ = (h : G) • sourceOpenCosetBasepoint G H := by
              rw [x.property]
              rfl
        _ = sourceOpenCosetBasepoint G H := by
              rw [← MulAction.mem_stabilizer_iff,
                sourceOpenCosetBasepoint_stabilizer]
              exact h.property⟩
  one_smul x := by
    apply Subtype.ext
    change (1 : G) • x.val = x.val
    exact one_smul G x.val
  mul_smul h k x := by
    apply Subtype.ext
    change ((h * k : H) : G) • x.val =
      (h : G) • ((k : G) • x.val)
    simpa only [Subgroup.coe_mul] using
      mul_smul (h : G) (k : G) x.val

/-- The definitionally distinct subtype carried by `H.toSubgroup` acts by
the same restricted `G`-action.  This is the group type used by the literal
quotient `(G x T)/H`. -/
noncomputable instance sourceOpenCosetSliceFiber_toSubgroup_mulAction :
    MulAction H.toSubgroup (SourceOpenCosetSliceFiber G H X) where
  smul h x :=
    ⟨(h : G) • x.val, by
      calc
        X.hom.hom.hom ((h : G) • x.val) =
            (h : G) • X.hom.hom.hom x.val := by
              exact ConcreteCategory.congr_hom
                (X.hom.hom.comm (h : G)) x.val
        _ = (h : G) • sourceOpenCosetBasepoint G H := by
              rw [x.property]
              rfl
        _ = sourceOpenCosetBasepoint G H := by
              rw [← MulAction.mem_stabilizer_iff,
                sourceOpenCosetBasepoint_stabilizer]
              exact h.property⟩
  one_smul x := by
    apply Subtype.ext
    change (1 : G) • x.val = x.val
    exact one_smul G x.val
  mul_smul h k x := by
    apply Subtype.ext
    change (((h * k : H.toSubgroup) : G) • x.val) =
      (h : G) • ((k : G) • x.val)
    simpa only [Subgroup.coe_mul] using
      mul_smul (h : G) (k : G) x.val

/-- The fiber over the identity coset is a finite continuous `H`-action. -/
noncomputable def action :
    ContAction FintypeCat.{u} H := by
  letI : TopologicalSpace (SourceOpenCosetSliceFiber G H X) := ⊥
  letI : DiscreteTopology (SourceOpenCosetSliceFiber G H X) := ⟨rfl⟩
  letI : IsTopologicalGroup H :=
    inferInstanceAs <| IsTopologicalGroup H.toSubgroup
  refine
    ⟨Action.FintypeCat.ofMulAction H
      (FintypeCat.of (SourceOpenCosetSliceFiber G H X)), ?_⟩
  change ContinuousSMul H (SourceOpenCosetSliceFiber G H X)
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  let U : Subgroup H :=
    (MulAction.stabilizer G x.val).comap H.toSubgroup.subtype
  have hU_open : IsOpen (U : Set H) := by
    change IsOpen (H.toSubgroup.subtype ⁻¹'
      (MulAction.stabilizer G x.val : Set G))
    haveI : ContinuousSMul G X.left.obj.V := X.left.property
    exact continuous_subtype_val.isOpen_preimage _
      (stabilizer_isOpen G x.val)
  apply Subgroup.isOpen_mono
    (H₁ := U)
    (H₂ := MulAction.stabilizer H x) _ hU_open
  intro h hh
  change (h : G) ∈ MulAction.stabilizer G x.val at hh
  rw [MulAction.mem_stabilizer_iff] at hh
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  exact hh

end SourceOpenCosetSliceFiber

/-- The underlying map on identity-coset fibers. -/
noncomputable def sourceOpenCosetSliceFiberMapFunction
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    {X Y : Over (sourceOpenCosetAction G H)} (f : X ⟶ Y) :
    SourceOpenCosetSliceFiber G H X →
      SourceOpenCosetSliceFiber G H Y :=
  fun x =>
    ⟨f.left.hom.hom x.val, by
      have hw :=
        ConcreteCategory.congr_hom (Over.w f) x.val
      exact hw.trans x.property⟩

/-- The raw equivariant map between the two finite `H`-actions on fibers. -/
noncomputable def sourceOpenCosetSliceFiberRawActionMap
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    {X Y : Over (sourceOpenCosetAction G H)} (f : X ⟶ Y) :
    Action.FintypeCat.ofMulAction H
        (FintypeCat.of (SourceOpenCosetSliceFiber G H X)) ⟶
      Action.FintypeCat.ofMulAction H
        (FintypeCat.of (SourceOpenCosetSliceFiber G H Y)) where
  hom := FintypeCat.homMk
    (sourceOpenCosetSliceFiberMapFunction G H f)
  comm h := by
    ext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      (f.left.hom.comm (h : G)) x.val

/-- A morphism in the slice restricts to an equivariant map of the fibers. -/
noncomputable def sourceOpenCosetSliceFiberMap
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    {X Y : Over (sourceOpenCosetAction G H)} (f : X ⟶ Y) :
    SourceOpenCosetSliceFiber.action G H X ⟶
      SourceOpenCosetSliceFiber.action G H Y := by
  apply ObjectProperty.homMk
  change
    Action.FintypeCat.ofMulAction H
        (FintypeCat.of (SourceOpenCosetSliceFiber G H X)) ⟶
      Action.FintypeCat.ofMulAction H
        (FintypeCat.of (SourceOpenCosetSliceFiber G H Y))
  exact sourceOpenCosetSliceFiberRawActionMap G H f

/-- The source fiber functor `X -> G/H |-> X_H`. -/
noncomputable def sourceSliceFiberFunctor
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    Over (sourceOpenCosetAction G H) ⥤
      ContAction FintypeCat.{u} H where
  obj X := SourceOpenCosetSliceFiber.action G H X
  map f := sourceOpenCosetSliceFiberMap G H f
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext x
    apply Subtype.ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext x
    apply Subtype.ext
    rfl

/-! ## The fiber of an induced action -/

/-- The explicit identity-coset fiber of the induced action. -/
noncomputable def SourceInducedIdentityFiber
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H) :=
  { q : SourceInducedSet G H.toSubgroup T.obj.V //
    SourceInducedSet.projection G H.toSubgroup T.obj.V q =
      (QuotientGroup.mk (1 : G) : G ⧸ H.toSubgroup) }

noncomputable instance sourceInducedIdentityFiber_fintype
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H) :
    Fintype (SourceInducedIdentityFiber G H T) := by
  letI : Fintype T.obj.V := FintypeCat.fintype
  letI : Finite (G ⧸ H.toSubgroup) :=
    H.toSubgroup.quotient_finite_of_isOpen H.isOpen
  letI : Fintype (SourceInducedSet G H.toSubgroup T.obj.V) :=
    Fintype.ofFinite _
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

/-- If `[g,t]` lies above the identity coset, then `g` belongs to `H`. -/
theorem sourceInducedIdentityFiber_first_mem
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (g : G) (t : T.obj.V)
    (hfiber :
      SourceInducedSet.projection G H.toSubgroup T.obj.V
          (SourceInducedSet.mk G H.toSubgroup T.obj.V g t) =
        (QuotientGroup.mk (1 : G) : G ⧸ H.toSubgroup)) :
    g ∈ H := by
  change (g : G ⧸ H.toSubgroup) =
    (QuotientGroup.mk (1 : G) : G ⧸ H.toSubgroup) at hfiber
  have hinv : g⁻¹ ∈ H.toSubgroup := by
    simpa only [mul_one] using QuotientGroup.eq.mp hfiber
  simpa only [inv_inv] using H.toSubgroup.inv_mem hinv

/-- The chosen representative of an induced identity-fiber class. -/
noncomputable def sourceInducedIdentityFiberRepresentative
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (q : SourceInducedIdentityFiber G H T) :
    G × T.obj.V :=
  q.val.out

theorem sourceInducedIdentityFiberRepresentative_eq
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (q : SourceInducedIdentityFiber G H T) :
    SourceInducedSet.mk G H.toSubgroup T.obj.V
        (sourceInducedIdentityFiberRepresentative G H T q).1
        (sourceInducedIdentityFiberRepresentative G H T q).2 =
      q.val :=
  Quotient.out_eq q.val

/-- The first coordinate of the chosen representative, regarded as an
element of `H` by the fiber equation. -/
noncomputable def sourceInducedIdentityFiberRepresentativeH
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (q : SourceInducedIdentityFiber G H T) :
    H := by
  let p := sourceInducedIdentityFiberRepresentative G H T q
  refine ⟨p.1, ?_⟩
  apply sourceInducedIdentityFiber_first_mem G H T p.1 p.2
  rw [sourceInducedIdentityFiberRepresentative_eq G H T q]
  exact q.property

/-- Evaluation of an identity-fiber class by `[g,t] |-> g.t`. -/
noncomputable def sourceInducedIdentityFiberToOriginal
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H) :
    SourceInducedIdentityFiber G H T → T.obj.V :=
  fun q =>
    sourceInducedIdentityFiberRepresentativeH G H T q •
      (sourceInducedIdentityFiberRepresentative G H T q).2

/-- The canonical class `[1,t]` in the identity-coset fiber. -/
noncomputable def sourceOriginalToInducedIdentityFiber
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H) :
    T.obj.V → SourceInducedIdentityFiber G H T :=
  fun t =>
    ⟨SourceInducedSet.mk G H.toSubgroup T.obj.V 1 t, rfl⟩

theorem sourceInducedIdentityFiberToOriginal_original
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H) (t : T.obj.V) :
    sourceInducedIdentityFiberToOriginal G H T
        (sourceOriginalToInducedIdentityFiber G H T t) = t := by
  let q :=
    sourceOriginalToInducedIdentityFiber G H T t
  let p :=
    sourceInducedIdentityFiberRepresentative G H T q
  let h :=
    sourceInducedIdentityFiberRepresentativeH G H T q
  have hp_eq :
      SourceInducedSet.mk G H.toSubgroup T.obj.V p.1 p.2 =
        SourceInducedSet.mk G H.toSubgroup T.obj.V 1 t := by
    exact sourceInducedIdentityFiberRepresentative_eq G H T q
  obtain ⟨k, hk_group, hk_value⟩ :=
    Quotient.exact hp_eq
  have hp_first : p.1 = (k⁻¹ : H) := by
    have hmul :=
      congrArg (fun g : G => g * (k : G)⁻¹) hk_group
    simpa only [one_mul, mul_assoc, mul_inv_cancel, mul_one] using hmul.symm
  have hh : h = k⁻¹ := by
    apply Subtype.ext
    exact hp_first
  change h • p.2 = t
  rw [hh]
  exact hk_value.symm

theorem sourceOriginalToInducedIdentityFiber_induced
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (q : SourceInducedIdentityFiber G H T) :
    sourceOriginalToInducedIdentityFiber G H T
        (sourceInducedIdentityFiberToOriginal G H T q) = q := by
  let p :=
    sourceInducedIdentityFiberRepresentative G H T q
  let h :=
    sourceInducedIdentityFiberRepresentativeH G H T q
  apply Subtype.ext
  change
    SourceInducedSet.mk G H.toSubgroup T.obj.V 1
        (h • p.2) = q.val
  calc
    SourceInducedSet.mk G H.toSubgroup T.obj.V 1 (h • p.2) =
        SourceInducedSet.mk G H.toSubgroup T.obj.V p.1 p.2 := by
          simpa [h, p,
            sourceInducedIdentityFiberRepresentativeH] using
            (SourceInducedSet.mk_eq_mk
              G H.toSubgroup T.obj.V 1 (h • p.2) h).symm
    _ = q.val :=
      sourceInducedIdentityFiberRepresentative_eq G H T q

/-- The source bijection between `T` and the identity-coset fiber of
`(G x T)/H`. -/
noncomputable def sourceInducedIdentityFiberEquiv
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H) :
    SourceInducedIdentityFiber G H T ≃ T.obj.V where
  toFun := sourceInducedIdentityFiberToOriginal G H T
  invFun := sourceOriginalToInducedIdentityFiber G H T
  left_inv := sourceOriginalToInducedIdentityFiber_induced G H T
  right_inv := sourceInducedIdentityFiberToOriginal_original G H T

namespace SourceInducedIdentityFiber

variable (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
variable (T : ContAction FintypeCat.{u} H)

/-- The identity-coset fiber inherits the `H`-action from the induced
`G`-action. -/
noncomputable instance sourceInducedIdentityFiber_mulAction :
    MulAction H (SourceInducedIdentityFiber G H T) where
  smul h q :=
    ⟨(h : G) • q.val, by
      rw [SourceInducedSet.projection_smul, q.property]
      rw [← MulAction.mem_stabilizer_iff,
        MulAction.stabilizer_quotient]
      exact h.property⟩
  one_smul q := by
    apply Subtype.ext
    exact one_smul G q.val
  mul_smul h k q := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using
      mul_smul (h : G) (k : G) q.val

end SourceInducedIdentityFiber

/-- The map `t |-> [1,t]` is `H`-equivariant. -/
theorem sourceOriginalToInducedIdentityFiber_smul
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (h : H) (t : T.obj.V) :
    sourceOriginalToInducedIdentityFiber G H T (h • t) =
      h • sourceOriginalToInducedIdentityFiber G H T t := by
  apply Subtype.ext
  have hleft :
      (sourceOriginalToInducedIdentityFiber G H T (h • t)).val =
        SourceInducedSet.mk G H.toSubgroup T.obj.V 1 (h • t) :=
    rfl
  have hright :
      (h • sourceOriginalToInducedIdentityFiber G H T t).val =
        (h : G) •
          SourceInducedSet.mk G H.toSubgroup T.obj.V 1 t :=
    rfl
  rw [hleft, hright]
  rw [SourceInducedSet.smul_mk, mul_one]
  simpa using
    (SourceInducedSet.mk_eq_mk
      G H.toSubgroup T.obj.V 1 (h • t) h).symm

/-- Evaluation `[g,t] |-> g.t` is `H`-equivariant. -/
theorem sourceInducedIdentityFiberToOriginal_smul
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (h : H) (q : SourceInducedIdentityFiber G H T) :
    sourceInducedIdentityFiberToOriginal G H T (h • q) =
      h • sourceInducedIdentityFiberToOriginal G H T q := by
  apply Function.LeftInverse.injective
    (sourceInducedIdentityFiberToOriginal_original G H T)
  rw [sourceOriginalToInducedIdentityFiber_induced]
  rw [sourceOriginalToInducedIdentityFiber_smul]
  rw [sourceOriginalToInducedIdentityFiber_induced]

/-- The action isomorphism identifying the fiber of an induced object with
the original continuous `H`-action. -/
noncomputable def sourceInducedFiberActionIso
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H) :
    (sourceInductionToSlice G H ⋙ sourceSliceFiberFunctor G H).obj T ≅ T := by
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ ?_
  · change
      FintypeCat.of (SourceInducedIdentityFiber G H T) ≅ T.obj.V
    exact FintypeCat.equivEquivIso
      (sourceInducedIdentityFiberEquiv G H T)
  · intro h
    ext q
    change
      sourceInducedIdentityFiberToOriginal G H T (h • q) =
        h • sourceInducedIdentityFiberToOriginal G H T q
    exact sourceInducedIdentityFiberToOriginal_smul G H T h q

/-! ## Evaluation of the induced fiber -/

/-- The source evaluation map `[g,x] |-> g.x` for the fiber of an arbitrary
slice object `X -> G/H`. -/
noncomputable def sourceInducedSliceFiberEvaluation
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (X : Over (sourceOpenCosetAction G H)) :
    SourceInducedSet G H.toSubgroup
        (SourceOpenCosetSliceFiber G H X) →
      X.left.obj.V :=
  Quotient.lift
    (fun p : G × SourceOpenCosetSliceFiber G H X =>
      p.1 • p.2.val)
    (by
      rintro a b ⟨h, hb1, hb2⟩
      change a.1 • a.2.val = b.1 • b.2.val
      have hb2val :
          b.2.val = (h⁻¹ : H.toSubgroup) • a.2.val :=
        congrArg Subtype.val hb2
      rw [hb1, hb2val]
      change
        a.1 • a.2.val =
          (a.1 * (h : G)) • ((h⁻¹ : H.toSubgroup) : G) •
            a.2.val
      rw [← mul_smul, Subgroup.coe_inv, mul_inv_cancel_right])

@[simp]
theorem sourceInducedSliceFiberEvaluation_mk
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (X : Over (sourceOpenCosetAction G H))
    (g : G) (x : SourceOpenCosetSliceFiber G H X) :
    sourceInducedSliceFiberEvaluation G H X
        (SourceInducedSet.mk G H.toSubgroup
          (SourceOpenCosetSliceFiber G H X) g x) =
      g • x.val :=
  rfl

theorem sourceInducedSliceFiberEvaluation_smul
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (X : Over (sourceOpenCosetAction G H))
    (g : G)
    (q : SourceInducedSet G H.toSubgroup
      (SourceOpenCosetSliceFiber G H X)) :
    sourceInducedSliceFiberEvaluation G H X (g • q) =
      g • sourceInducedSliceFiberEvaluation G H X q := by
  induction q using Quotient.inductionOn with
  | _ p =>
      change (g * p.1) • p.2.val =
        g • (p.1 • p.2.val)
      exact mul_smul g p.1 p.2.val

/-- Evaluation lies over the source projection to `G/H`. -/
theorem sourceInducedSliceFiberEvaluation_over
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (X : Over (sourceOpenCosetAction G H))
    (q : SourceInducedSet G H.toSubgroup
      (SourceOpenCosetSliceFiber G H X)) :
    X.hom.hom.hom (sourceInducedSliceFiberEvaluation G H X q) =
      SourceInducedSet.projection G H.toSubgroup
        (SourceOpenCosetSliceFiber G H X) q := by
  induction q using Quotient.inductionOn with
  | _ p =>
      calc
        X.hom.hom.hom (p.1 • p.2.val) =
            p.1 • X.hom.hom.hom p.2.val := by
              exact ConcreteCategory.congr_hom
                (X.hom.hom.comm p.1) p.2.val
        _ =
            SourceInducedSet.projection G H.toSubgroup
              (SourceOpenCosetSliceFiber G H X)
              (SourceInducedSet.mk G H.toSubgroup
                (SourceOpenCosetSliceFiber G H X) p.1 p.2) :=
          by
            rw [p.2.property]
            exact sourceOpenCoset_smul_basepoint G H p.1

/-- Evaluation is surjective: move an arbitrary point back along a chosen
representative of its image coset. -/
theorem sourceInducedSliceFiberEvaluation_surjective
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (X : Over (sourceOpenCosetAction G H)) :
    Function.Surjective (sourceInducedSliceFiberEvaluation G H X) := by
  intro y
  let coset : G ⧸ H.toSubgroup := X.hom.hom.hom y
  let g : G := coset.out
  have hg_coset :
      (g : G ⧸ H.toSubgroup) = coset :=
    QuotientGroup.out_eq' coset
  let x : SourceOpenCosetSliceFiber G H X :=
    ⟨g⁻¹ • y, by
      change
        X.hom.hom.hom (g⁻¹ • y) =
          (QuotientGroup.mk (1 : G) : G ⧸ H.toSubgroup)
      calc
        X.hom.hom.hom (g⁻¹ • y) =
            g⁻¹ • X.hom.hom.hom y := by
              exact ConcreteCategory.congr_hom
                (X.hom.hom.comm g⁻¹) y
        _ = g⁻¹ • coset := rfl
        _ = g⁻¹ • (g : G ⧸ H.toSubgroup) := by
              rw [← hg_coset]
        _ = (QuotientGroup.mk (1 : G) :
            G ⧸ H.toSubgroup) := by
              change
                (QuotientGroup.mk (g⁻¹ * g) :
                    G ⧸ H.toSubgroup) =
                  QuotientGroup.mk (1 : G)
              rw [inv_mul_cancel]⟩
  refine
    ⟨SourceInducedSet.mk G H.toSubgroup
      (SourceOpenCosetSliceFiber G H X) g x, ?_⟩
  change g • (g⁻¹ • y) = y
  simp only [← mul_smul, mul_inv_cancel, one_smul]

/-- Evaluation is injective; equality after evaluation produces exactly the
`H`-relation identifying the two representatives. -/
theorem sourceInducedSliceFiberEvaluation_injective
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (X : Over (sourceOpenCosetAction G H)) :
    Function.Injective (sourceInducedSliceFiberEvaluation G H X) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ a =>
      induction r using Quotient.inductionOn with
      | _ b =>
          have hcoset :
              (a.1 : G ⧸ H.toSubgroup) =
                (b.1 : G ⧸ H.toSubgroup) := by
            have hmap :=
              congrArg X.hom.hom.hom hqr
            simpa only [
              sourceInducedSliceFiberEvaluation_mk,
              sourceInducedSliceFiberEvaluation_over] using hmap
          have hmem :
              a.1⁻¹ * b.1 ∈ H.toSubgroup :=
            QuotientGroup.eq.mp hcoset
          let h : H.toSubgroup := ⟨a.1⁻¹ * b.1, hmem⟩
          apply Quotient.sound
          refine ⟨h, ?_, ?_⟩
          · change b.1 = a.1 * (a.1⁻¹ * b.1)
            group
          · apply Subtype.ext
            have hcancel :=
              congrArg (fun z : X.left.obj.V => a.1⁻¹ • z) hqr
            change
              a.1⁻¹ • (a.1 • a.2.val) =
                a.1⁻¹ • (b.1 • b.2.val) at hcancel
            have ha :
                a.2.val = (a.1⁻¹ * b.1) • b.2.val := by
              simpa only [← mul_smul, inv_mul_cancel, one_smul] using
                hcancel
            have hinv :=
              congrArg (fun z : X.left.obj.V =>
                (a.1⁻¹ * b.1)⁻¹ • z) ha
            simpa only [← mul_smul, inv_mul_cancel, one_smul] using
              hinv.symm

theorem sourceInducedSliceFiberEvaluation_bijective
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (X : Over (sourceOpenCosetAction G H)) :
    Function.Bijective (sourceInducedSliceFiberEvaluation G H X) :=
  ⟨sourceInducedSliceFiberEvaluation_injective G H X,
    sourceInducedSliceFiberEvaluation_surjective G H X⟩

/-- Evaluation is an equivalence of the underlying finite sets. -/
noncomputable def sourceInducedSliceFiberEvaluationEquiv
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (X : Over (sourceOpenCosetAction G H)) :
    SourceInducedSet G H.toSubgroup
        (SourceOpenCosetSliceFiber G H X) ≃
      X.left.obj.V :=
  Equiv.ofBijective
    (sourceInducedSliceFiberEvaluation G H X)
    (sourceInducedSliceFiberEvaluation_bijective G H X)

/-- Evaluation is an isomorphism of finite continuous `G`-actions. -/
noncomputable def sourceInducedSliceFiberActionIso
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (X : Over (sourceOpenCosetAction G H)) :
    sourceInducedAction G H
        (SourceOpenCosetSliceFiber.action G H X) ≅
      X.left := by
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ ?_
  · change
      FintypeCat.of
          (SourceInducedSet G H.toSubgroup
            (SourceOpenCosetSliceFiber G H X)) ≅
        X.left.obj.V
    exact FintypeCat.equivEquivIso
      (sourceInducedSliceFiberEvaluationEquiv G H X)
  · intro g
    ext q
    change
      sourceInducedSliceFiberEvaluation G H X (g • q) =
        g • sourceInducedSliceFiberEvaluation G H X q
    exact sourceInducedSliceFiberEvaluation_smul G H X g q

/-- The induced identity fiber recovers an arbitrary object of the slice
over `G/H`. -/
noncomputable def sourceInducedSliceFiberOverIso
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (X : Over (sourceOpenCosetAction G H)) :
    (sourceSliceFiberFunctor G H ⋙ sourceInductionToSlice G H).obj X ≅
      X := by
  refine Over.isoMk (sourceInducedSliceFiberActionIso G H X) ?_
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext q
  exact sourceInducedSliceFiberEvaluation_over G H X q

/-! ## The source slice equivalence -/

/-- The fiber evaluation is natural in finite continuous `H`-actions. -/
theorem sourceInducedFiberActionIso_naturality
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    {T U : ContAction FintypeCat.{u} H} (f : T ⟶ U) :
    (sourceInductionToSlice G H ⋙ sourceSliceFiberFunctor G H).map f ≫
        (sourceInducedFiberActionIso G H U).hom =
      (sourceInducedFiberActionIso G H T).hom ≫ f := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext q
  change
    sourceInducedIdentityFiberToOriginal G H U
        (sourceOpenCosetSliceFiberMapFunction G H
          ((sourceInductionToSlice G H).map f) q) =
      f.hom.hom (sourceInducedIdentityFiberToOriginal G H T q)
  have hmap :=
    congrArg
      (sourceOpenCosetSliceFiberMapFunction G H
        ((sourceInductionToSlice G H).map f))
      (sourceOriginalToInducedIdentityFiber_induced G H T q)
  have hfiber :
      sourceOpenCosetSliceFiberMapFunction G H
          ((sourceInductionToSlice G H).map f) q =
        sourceOriginalToInducedIdentityFiber G H U
          (f.hom.hom
            (sourceInducedIdentityFiberToOriginal G H T q)) := by
    exact hmap.symm
  rw [hfiber]
  exact sourceInducedIdentityFiberToOriginal_original G H U _

/-- Induction followed by the identity-coset fiber functor is naturally
isomorphic to the identity on `B(H)`. -/
noncomputable def sourceInducedFiberActionNatIso
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    sourceInductionToSlice G H ⋙ sourceSliceFiberFunctor G H ≅
      𝟭 (ContAction FintypeCat.{u} H) :=
  NatIso.ofComponents
    (sourceInducedFiberActionIso G H)
    (fun f => sourceInducedFiberActionIso_naturality G H f)

/-- Evaluation of the induced identity-coset fiber is natural in objects of
the slice over `G/H`. -/
theorem sourceInducedSliceFiberOverIso_naturality
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    {X Y : Over (sourceOpenCosetAction G H)} (f : X ⟶ Y) :
    (sourceSliceFiberFunctor G H ⋙ sourceInductionToSlice G H).map f ≫
        (sourceInducedSliceFiberOverIso G H Y).hom =
      (sourceInducedSliceFiberOverIso G H X).hom ≫ f := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext q
  induction q using Quotient.inductionOn with
  | _ p =>
      change
        p.1 • f.left.hom.hom p.2.val =
          f.left.hom.hom (p.1 • p.2.val)
      exact
        (ConcreteCategory.congr_hom
          (f.left.hom.comm p.1) p.2.val).symm

/-- Restriction to the identity-coset fiber followed by induction is
naturally isomorphic to the identity on the slice over `G/H`. -/
noncomputable def sourceInducedSliceFiberOverNatIso
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    sourceSliceFiberFunctor G H ⋙ sourceInductionToSlice G H ≅
      𝟭 (Over (sourceOpenCosetAction G H)) :=
  NatIso.ofComponents
    (sourceInducedSliceFiberOverIso G H)
    (fun f => sourceInducedSliceFiberOverIso_naturality G H f)

/-- Proposition 1.2.1(v) of *The Geometry of Anabelioids*: for every open
subgroup `H ≤ G`, the anabelioid of finite continuous `H`-sets is
equivalent to the slice of `B(G)` over the transitive object `G/H`. -/
noncomputable def sourceOpenCosetSliceEquivalence
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    ContAction FintypeCat.{u} H ≌
      Over (sourceOpenCosetAction G H) :=
  CategoryTheory.Equivalence.mk
    (sourceInductionToSlice G H)
    (sourceSliceFiberFunctor G H)
    (sourceInducedFiberActionNatIso G H).symm
    (sourceInducedSliceFiberOverNatIso G H)

/-! ## The slice adjunction and finite-etale factorization -/

/-- Proposition 1.2.1's functor `i_S^* : B(G) → B(G)_S`, obtained by
taking the product with `S` and projecting to `S`. -/
noncomputable def sourceSliceProductFunctor
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :
    ContAction FintypeCat.{u} G ⥤ Over S :=
  Over.star S

/-- Proposition 1.2.1(ii): the forgetful extension functor `j_S` is left
adjoint to product with `S`. -/
noncomputable def sourceSliceForgetAdjProduct
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :
    Over.forget S ⊣ sourceSliceProductFunctor G S :=
  Over.forgetAdjStar S

/-- Product with `S` preserves finite limits. -/
noncomputable instance sourceSliceProduct_preservesFiniteLimits
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :
    Limits.PreservesFiniteLimits (sourceSliceProductFunctor G S) := by
  letI :=
    (sourceSliceForgetAdjProduct G S).rightAdjoint_preservesLimits
  infer_instance

/-! ## Dependent sections and arbitrary-base exactness -/

/-- A dependent section of an object `T -> S` in the slice is a choice of a
point of every fiber. -/
structure SourceDependentSection
    {G : ProfiniteGrp.{u}} {S : ContAction FintypeCat.{u} G}
    (T : Over S) where
  toFun : S.obj.V → T.left.obj.V
  mapsToFiber : ∀ s, T.hom.hom.hom (toFun s) = s

namespace SourceDependentSection

variable {G : ProfiniteGrp.{u}} {S : ContAction FintypeCat.{u} G}
variable (T : Over S)

instance : FunLike (SourceDependentSection T) S.obj.V T.left.obj.V where
  coe := toFun
  coe_injective' first second h := by
    cases first
    cases second
    cases h
    rfl

@[ext]
theorem ext
    {first second : SourceDependentSection T}
    (h : ∀ s, first s = second s) :
    first = second :=
  DFunLike.ext _ _ h

instance : Finite (SourceDependentSection T) :=
  Finite.of_injective
    SourceDependentSection.toFun
    (fun _ _ h => SourceDependentSection.ext T (congrFun h))

noncomputable instance : Fintype (SourceDependentSection T) :=
  Fintype.ofFinite _

/-- Conjugation transports a dependent section to a dependent section. -/
instance : SMul G (SourceDependentSection T) where
  smul g value :=
    { toFun := fun s => g • value (g⁻¹ • s)
      mapsToFiber := fun s => by
        calc
          T.hom.hom.hom (g • value (g⁻¹ • s)) =
              g • T.hom.hom.hom (value (g⁻¹ • s)) := by
                exact ConcreteCategory.congr_hom
                  (T.hom.hom.comm g) (value (g⁻¹ • s))
          _ = g • (g⁻¹ • s) := by
            exact congrArg (g • ·)
              (value.mapsToFiber (g⁻¹ • s))
          _ = s := by simp only [← mul_smul, mul_inv_cancel, one_smul] }

instance : MulAction G (SourceDependentSection T) where
  one_smul value := by
    ext s
    change (1 : G) • value ((1 : G)⁻¹ • s) = value s
    simp
  mul_smul first second value := by
    ext s
    change
      (first * second) • value ((first * second)⁻¹ • s) =
        first • (second • value (second⁻¹ • (first⁻¹ • s)))
    simp only [mul_inv_rev, mul_smul]

@[simp]
theorem smul_apply
    (g : G) (value : SourceDependentSection T) (s : S.obj.V) :
    (g • value) s = g • value (g⁻¹ • s) :=
  rfl

noncomputable instance : TopologicalSpace (SourceDependentSection T) := ⊥

instance : DiscreteTopology (SourceDependentSection T) := ⟨rfl⟩

end SourceDependentSection

/-- The finite intersection of the pointwise stabilizers of an action. -/
def sourceActionGlobalKernel
    (G : ProfiniteGrp.{u}) (X : ContAction FintypeCat.{u} G) :
    Subgroup G :=
  ⨅ x : X.obj.V, MulAction.stabilizer G x

/-- The global kernel of a finite continuous action is open. -/
theorem sourceActionGlobalKernel_isOpen
    (G : ProfiniteGrp.{u}) (X : ContAction FintypeCat.{u} G) :
    IsOpen (sourceActionGlobalKernel G X : Set G) := by
  rw [sourceActionGlobalKernel, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun x => by
    haveI : ContinuousSMul G X.obj.V := X.property
    exact stabilizer_isOpen G x

/-- An element of the global kernel fixes every point. -/
theorem sourceActionGlobalKernel_fixes
    (G : ProfiniteGrp.{u}) (X : ContAction FintypeCat.{u} G)
    {g : G} (hg : g ∈ sourceActionGlobalKernel G X)
    (x : X.obj.V) :
    g • x = x := by
  rw [← MulAction.mem_stabilizer_iff]
  exact Subgroup.mem_iInf.mp hg x

/-- The dependent-section action is continuous.  The stabilizer of every
section contains the intersection of the global kernels on the base and total
space. -/
theorem sourceDependentSection_continuous
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (T : Over S) :
    ContinuousSMul G (SourceDependentSection T) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro value
  let K : Subgroup G :=
    sourceActionGlobalKernel G S ⊓
      sourceActionGlobalKernel G T.left
  have hK_open : IsOpen (K : Set G) := by
    exact
      (sourceActionGlobalKernel_isOpen G S).inter
        (sourceActionGlobalKernel_isOpen G T.left)
  apply Subgroup.isOpen_mono
    (H₁ := K)
    (H₂ := MulAction.stabilizer G value) _ hK_open
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  apply SourceDependentSection.ext
  intro s
  have hg_base :
      g ∈ sourceActionGlobalKernel G S :=
    (Subgroup.mem_inf.mp hg).1
  have hg_total :
      g ∈ sourceActionGlobalKernel G T.left :=
    (Subgroup.mem_inf.mp hg).2
  have hginv_base :
      g⁻¹ ∈ sourceActionGlobalKernel G S :=
    (sourceActionGlobalKernel G S).inv_mem hg_base
  change g • value (g⁻¹ • s) = value s
  rw [sourceActionGlobalKernel_fixes G S hginv_base s]
  exact
    sourceActionGlobalKernel_fixes
      G T.left hg_total (value s)

/-- The finite continuous action of dependent sections of `T -> S`. -/
noncomputable def sourceDependentSectionAction
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (T : Over S) :
    ContAction FintypeCat.{u} G := by
  exact
    ⟨Action.FintypeCat.ofMulAction G
      (FintypeCat.of (SourceDependentSection T)),
      sourceDependentSection_continuous G S T⟩

/-- Postcomposition maps dependent sections along a morphism in the slice. -/
def sourceDependentSectionMapFunction
    {G : ProfiniteGrp.{u}} {S : ContAction FintypeCat.{u} G}
    {T U : Over S} (f : T ⟶ U) :
    SourceDependentSection T → SourceDependentSection U :=
  fun value =>
    { toFun := fun s => f.left.hom.hom (value s)
      mapsToFiber := fun s => by
        have hwFiber :=
          congrArg
            (fun map : T.left ⟶ S =>
              (continuousActionFiber G).map map)
            (Over.w f)
        dsimp only at hwFiber
        rw [Functor.map_comp] at hwFiber
        have hpoint :=
          ConcreteCategory.congr_hom hwFiber (value s)
        exact hpoint.trans (value.mapsToFiber s) }

@[simp]
theorem sourceDependentSectionMapFunction_apply
    {G : ProfiniteGrp.{u}} {S : ContAction FintypeCat.{u} G}
    {T U : Over S} (f : T ⟶ U)
    (value : SourceDependentSection T) (s : S.obj.V) :
    sourceDependentSectionMapFunction f value s =
      f.left.hom.hom (value s) :=
  rfl

/-- Postcomposition of dependent sections is equivariant. -/
theorem sourceDependentSectionMapFunction_equivariant
    {G : ProfiniteGrp.{u}} {S : ContAction FintypeCat.{u} G}
    {T U : Over S} (f : T ⟶ U)
    (g : G) (value : SourceDependentSection T) :
    sourceDependentSectionMapFunction f (g • value) =
      g • sourceDependentSectionMapFunction f value := by
  apply SourceDependentSection.ext
  intro s
  change
    f.left.hom.hom (g • value (g⁻¹ • s)) =
      g • f.left.hom.hom (value (g⁻¹ • s))
  exact ConcreteCategory.congr_hom
    (f.left.hom.comm g) (value (g⁻¹ • s))

/-- Postcomposition as a morphism of finite continuous actions. -/
noncomputable def sourceDependentSectionMap
    {G : ProfiniteGrp.{u}} {S : ContAction FintypeCat.{u} G}
    {T U : Over S} (f : T ⟶ U) :
    sourceDependentSectionAction G S T ⟶
      sourceDependentSectionAction G S U :=
  ObjectProperty.homMk
    ({ hom :=
        FintypeCat.homMk
          (sourceDependentSectionMapFunction f)
       comm := fun g => by
         ext value
         exact
           sourceDependentSectionMapFunction_equivariant
             f g value } :
      (sourceDependentSectionAction G S T).obj ⟶
        (sourceDependentSectionAction G S U).obj)

/-- The dependent-section construction as a functor from the slice. -/
noncomputable def sourceDependentSectionFunctor
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :
    Over S ⥤ ContAction FintypeCat.{u} G where
  obj := sourceDependentSectionAction G S
  map := sourceDependentSectionMap
  map_id T := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext value
    apply SourceDependentSection.ext
    intro s
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext value
    apply SourceDependentSection.ext
    intro s
    rfl

/-- The chosen categorical product of two continuous actions, compared with
the ordinary product of their underlying finite sets. -/
noncomputable def sourceActionProductEquiv
    (G : ProfiniteGrp.{u})
    (first second : ContAction FintypeCat.{u} G) :
    (first ⨯ second).obj.V ≃ first.obj.V × second.obj.V := by
  letI :
      PreservesLimit (pair first second)
        (forget (ContAction FintypeCat.{u} G)) := by
    change
      PreservesLimit (pair first second)
        (continuousActionFiber G ⋙ FintypeCat.incl)
    infer_instance
  exact Concrete.prodEquiv first second

@[simp]
theorem sourceActionProductEquiv_fst
    (G : ProfiniteGrp.{u})
    (first second : ContAction FintypeCat.{u} G)
    (point : (first ⨯ second).obj.V) :
    (sourceActionProductEquiv G first second point).1 =
      (prod.fst : first ⨯ second ⟶ first).hom.hom point := by
  letI :
      PreservesLimit (pair first second)
        (forget (ContAction FintypeCat.{u} G)) := by
    change
      PreservesLimit (pair first second)
        (continuousActionFiber G ⋙ FintypeCat.incl)
    infer_instance
  exact Concrete.prodEquiv_apply_fst first second point

@[simp]
theorem sourceActionProductEquiv_snd
    (G : ProfiniteGrp.{u})
    (first second : ContAction FintypeCat.{u} G)
    (point : (first ⨯ second).obj.V) :
    (sourceActionProductEquiv G first second point).2 =
      (prod.snd : first ⨯ second ⟶ second).hom.hom point := by
  letI :
      PreservesLimit (pair first second)
        (forget (ContAction FintypeCat.{u} G)) := by
    change
      PreservesLimit (pair first second)
        (continuousActionFiber G ⋙ FintypeCat.incl)
    infer_instance
  exact Concrete.prodEquiv_apply_snd first second point

/-- The product comparison is equivariant. -/
theorem sourceActionProductEquiv_smul
    (G : ProfiniteGrp.{u})
    (first second : ContAction FintypeCat.{u} G)
    (g : G) (point : (first ⨯ second).obj.V) :
    sourceActionProductEquiv G first second (g • point) =
      (g • (sourceActionProductEquiv G first second point).1,
        g • (sourceActionProductEquiv G first second point).2) := by
  apply Prod.ext
  · rw [sourceActionProductEquiv_fst,
      sourceActionProductEquiv_fst]
    exact ConcreteCategory.congr_hom
      ((prod.fst : first ⨯ second ⟶ first).hom.comm g) point
  · rw [sourceActionProductEquiv_snd,
      sourceActionProductEquiv_snd]
    exact ConcreteCategory.congr_hom
      ((prod.snd : first ⨯ second ⟶ second).hom.comm g) point

/-- Pair two points in the chosen categorical product. -/
noncomputable def sourceActionProductMk
    (G : ProfiniteGrp.{u})
    (first second : ContAction FintypeCat.{u} G)
    (firstPoint : first.obj.V) (secondPoint : second.obj.V) :
    (first ⨯ second).obj.V :=
  (sourceActionProductEquiv G first second).symm
    (firstPoint, secondPoint)

@[simp]
theorem sourceActionProductEquiv_mk
    (G : ProfiniteGrp.{u})
    (first second : ContAction FintypeCat.{u} G)
    (firstPoint : first.obj.V) (secondPoint : second.obj.V) :
    sourceActionProductEquiv G first second
        (sourceActionProductMk G first second firstPoint secondPoint) =
      (firstPoint, secondPoint) :=
  Equiv.apply_symm_apply _ _

@[simp]
theorem sourceActionProductMk_fst
    (G : ProfiniteGrp.{u})
    (first second : ContAction FintypeCat.{u} G)
    (firstPoint : first.obj.V) (secondPoint : second.obj.V) :
    (prod.fst : first ⨯ second ⟶ first).hom.hom
        (sourceActionProductMk G first second firstPoint secondPoint) =
      firstPoint := by
  rw [← sourceActionProductEquiv_fst]
  exact congrArg Prod.fst
    (sourceActionProductEquiv_mk
      G first second firstPoint secondPoint)

@[simp]
theorem sourceActionProductMk_snd
    (G : ProfiniteGrp.{u})
    (first second : ContAction FintypeCat.{u} G)
    (firstPoint : first.obj.V) (secondPoint : second.obj.V) :
    (prod.snd : first ⨯ second ⟶ second).hom.hom
        (sourceActionProductMk G first second firstPoint secondPoint) =
      secondPoint := by
  rw [← sourceActionProductEquiv_snd]
  exact congrArg Prod.snd
    (sourceActionProductEquiv_mk
      G first second firstPoint secondPoint)

@[simp]
theorem sourceActionProductMk_smul
    (G : ProfiniteGrp.{u})
    (first second : ContAction FintypeCat.{u} G)
    (g : G)
    (firstPoint : first.obj.V) (secondPoint : second.obj.V) :
    g • sourceActionProductMk G first second firstPoint secondPoint =
      sourceActionProductMk G first second
        (g • firstPoint) (g • secondPoint) := by
  apply (sourceActionProductEquiv G first second).injective
  rw [sourceActionProductEquiv_smul]
  simp only [sourceActionProductEquiv_mk]

/-- The structure map of the object `S x X -> S` is the first product
projection. -/
theorem sourceSliceProduct_hom_eq_fst
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G) :
    ((sourceSliceProductFunctor G S).obj X).hom =
      (prod.fst : S ⨯ X ⟶ S) := by
  dsimp only [sourceSliceProductFunctor]
  change
    prod.lift prod.fst (𝟙 (S ⨯ X)) ≫ prod.fst =
      (prod.fst : S ⨯ X ⟶ S)
  exact prod.lift_fst _ _

/-- Currying an arrow `S x X -> T` over `S` produces an ordinary function
from `X` to the dependent sections of `T -> S`. -/
noncomputable def sourceSliceHomToDependentSectionFunction
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G)
    (T : Over S)
    (f : (sourceSliceProductFunctor G S).obj X ⟶ T) :
    X.obj.V → SourceDependentSection T :=
  fun x =>
    { toFun := fun s =>
        f.left.hom.hom
          (sourceActionProductMk G S X s x)
      mapsToFiber := fun s => by
        let point :=
          sourceActionProductMk G S X s x
        have hwFiber :=
          congrArg
            (fun map :
                ((sourceSliceProductFunctor G S).obj X).left ⟶ S =>
              (continuousActionFiber G).map map)
            (Over.w f)
        dsimp only at hwFiber
        rw [Functor.map_comp] at hwFiber
        have hpoint :=
          ConcreteCategory.congr_hom hwFiber point
        calc
          T.hom.hom.hom (f.left.hom.hom point) =
              ((sourceSliceProductFunctor G S).obj X).hom.hom.hom
                point :=
            hpoint
          _ =
              (prod.fst : S ⨯ X ⟶ S).hom.hom point := by
            exact congrArg
              (fun map : (S ⨯ X) ⟶ S =>
                map.hom.hom point)
              (sourceSliceProduct_hom_eq_fst G S X)
          _ = s :=
            sourceActionProductMk_fst G S X s x }

@[simp]
theorem sourceSliceHomToDependentSectionFunction_apply
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G)
    (T : Over S)
    (f : (sourceSliceProductFunctor G S).obj X ⟶ T)
    (x : X.obj.V) (s : S.obj.V) :
    sourceSliceHomToDependentSectionFunction G S X T f x s =
      f.left.hom.hom
        (sourceActionProductMk G S X s x) :=
  rfl

/-- The curried function is equivariant. -/
theorem sourceSliceHomToDependentSectionFunction_equivariant
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G)
    (T : Over S)
    (f : (sourceSliceProductFunctor G S).obj X ⟶ T)
    (g : G) (x : X.obj.V) :
    sourceSliceHomToDependentSectionFunction G S X T f (g • x) =
      g • sourceSliceHomToDependentSectionFunction G S X T f x := by
  apply SourceDependentSection.ext
  intro s
  change
    f.left.hom.hom
        (sourceActionProductMk G S X s (g • x)) =
      g •
        f.left.hom.hom
          (sourceActionProductMk G S X (g⁻¹ • s) x)
  have hpair :
      g • sourceActionProductMk G S X (g⁻¹ • s) x =
        sourceActionProductMk G S X s (g • x) := by
    rw [sourceActionProductMk_smul]
    simp only [← mul_smul, mul_inv_cancel, one_smul]
  calc
    f.left.hom.hom
          (sourceActionProductMk G S X s (g • x)) =
        f.left.hom.hom
          (g •
            sourceActionProductMk G S X (g⁻¹ • s) x) :=
      congrArg f.left.hom.hom hpair.symm
    _ =
        g •
          f.left.hom.hom
            (sourceActionProductMk G S X (g⁻¹ • s) x) :=
      ConcreteCategory.congr_hom
        (f.left.hom.comm g)
        (sourceActionProductMk G S X (g⁻¹ • s) x)

/-- Currying as a morphism of finite continuous actions. -/
noncomputable def sourceSliceHomToDependentSection
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G)
    (T : Over S)
    (f : (sourceSliceProductFunctor G S).obj X ⟶ T) :
    X ⟶ (sourceDependentSectionFunctor G S).obj T :=
  ObjectProperty.homMk
    ({ hom :=
        FintypeCat.homMk
          (sourceSliceHomToDependentSectionFunction G S X T f)
       comm := fun g => by
         ext x
         exact
           sourceSliceHomToDependentSectionFunction_equivariant
             G S X T f g x } :
      X.obj ⟶
        ((sourceDependentSectionFunctor G S).obj T).obj)

/-- Evaluating a family of dependent sections at the two coordinates of
`S x X` gives the inverse uncurrying function. -/
noncomputable def sourceDependentSectionHomToSliceFunction
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G)
    (T : Over S)
    (f : X ⟶ (sourceDependentSectionFunctor G S).obj T) :
    (S ⨯ X).obj.V → T.left.obj.V :=
  fun point =>
    let coordinates :=
      sourceActionProductEquiv G S X point
    (show SourceDependentSection T from
      f.hom.hom coordinates.2) coordinates.1

@[simp]
theorem sourceDependentSectionHomToSliceFunction_mk
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G)
    (T : Over S)
    (f : X ⟶ (sourceDependentSectionFunctor G S).obj T)
    (s : S.obj.V) (x : X.obj.V) :
    sourceDependentSectionHomToSliceFunction G S X T f
        (sourceActionProductMk G S X s x) =
      (show SourceDependentSection T from
        f.hom.hom x) s := by
  simp only [sourceDependentSectionHomToSliceFunction,
    sourceActionProductEquiv_mk]

/-- Evaluation of an equivariant family of sections is equivariant. -/
theorem sourceDependentSectionHomToSliceFunction_equivariant
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G)
    (T : Over S)
    (f : X ⟶ (sourceDependentSectionFunctor G S).obj T)
    (g : G) (point : (S ⨯ X).obj.V) :
    sourceDependentSectionHomToSliceFunction G S X T f
        (g • point) =
      g • sourceDependentSectionHomToSliceFunction G S X T f point := by
  let coordinates :=
    sourceActionProductEquiv G S X point
  have hcoordinates :
      sourceActionProductEquiv G S X (g • point) =
        (g • coordinates.1, g • coordinates.2) :=
    sourceActionProductEquiv_smul G S X g point
  have hmap :
      f.hom.hom (g • coordinates.2) =
        g • f.hom.hom coordinates.2 :=
    ConcreteCategory.congr_hom
      (f.hom.comm g) coordinates.2
  change
    (show SourceDependentSection T from
      f.hom.hom
        (sourceActionProductEquiv G S X (g • point)).2)
        (sourceActionProductEquiv G S X (g • point)).1 =
      g •
        (show SourceDependentSection T from
          f.hom.hom coordinates.2) coordinates.1
  rw [hcoordinates]
  change
    (show SourceDependentSection T from
      f.hom.hom (g • coordinates.2)) (g • coordinates.1) =
      g •
        (show SourceDependentSection T from
          f.hom.hom coordinates.2) coordinates.1
  rw [hmap]
  change
    (g •
      (show SourceDependentSection T from
        f.hom.hom coordinates.2)) (g • coordinates.1) =
      g •
        (show SourceDependentSection T from
          f.hom.hom coordinates.2) coordinates.1
  rw [SourceDependentSection.smul_apply]
  simp only [← mul_smul, inv_mul_cancel, one_smul]

/-- Evaluation as a morphism of continuous `G`-actions. -/
noncomputable def sourceDependentSectionHomToProductAction
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G)
    (T : Over S)
    (f : X ⟶ (sourceDependentSectionFunctor G S).obj T) :
    S ⨯ X ⟶ T.left :=
  ObjectProperty.homMk
    ({ hom :=
        FintypeCat.homMk
          (sourceDependentSectionHomToSliceFunction G S X T f)
       comm := fun g => by
         ext point
         exact
           sourceDependentSectionHomToSliceFunction_equivariant
             G S X T f g point } :
      (S ⨯ X).obj ⟶ T.left.obj)

/-- Uncurrying an equivariant family of dependent sections gives an arrow in
the slice over `S`. -/
noncomputable def sourceDependentSectionHomToSlice
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G)
    (T : Over S)
    (f : X ⟶ (sourceDependentSectionFunctor G S).obj T) :
    (sourceSliceProductFunctor G S).obj X ⟶ T :=
  Over.homMk
    (sourceDependentSectionHomToProductAction G S X T f)
    (by
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      ext point
      let coordinates :=
        sourceActionProductEquiv G S X point
      change
        T.hom.hom.hom
            (sourceDependentSectionHomToSliceFunction
              G S X T f point) =
          ((sourceSliceProductFunctor G S).obj X).hom.hom.hom
            point
      calc
        T.hom.hom.hom
              (sourceDependentSectionHomToSliceFunction
                G S X T f point) =
            coordinates.1 :=
          (show SourceDependentSection T from
            f.hom.hom coordinates.2).mapsToFiber coordinates.1
        _ =
            (prod.fst : S ⨯ X ⟶ S).hom.hom point :=
          sourceActionProductEquiv_fst G S X point
        _ =
            ((sourceSliceProductFunctor G S).obj X).hom.hom.hom
              point := by
          exact congrArg
            (fun map : (S ⨯ X) ⟶ S =>
              map.hom.hom point)
            (sourceSliceProduct_hom_eq_fst G S X).symm)

/-- Uncurrying after currying recovers the original arrow over `S`. -/
theorem sourceSliceDependentSection_leftInverse
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G)
    (T : Over S)
    (f : (sourceSliceProductFunctor G S).obj X ⟶ T) :
    sourceDependentSectionHomToSlice G S X T
        (sourceSliceHomToDependentSection G S X T f) =
      f := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext point
  let coordinates :=
    sourceActionProductEquiv G S X point
  have hpoint :
      sourceActionProductMk G S X
          coordinates.1 coordinates.2 =
        point :=
    (sourceActionProductEquiv G S X).symm_apply_apply point
  change
    (sourceSliceHomToDependentSectionFunction
      G S X T f coordinates.2) coordinates.1 =
      f.left.hom.hom point
  rw [sourceSliceHomToDependentSectionFunction_apply]
  exact congrArg f.left.hom.hom hpoint

/-- Currying after uncurrying recovers the original equivariant family of
dependent sections. -/
theorem sourceSliceDependentSection_rightInverse
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G)
    (T : Over S)
    (f : X ⟶ (sourceDependentSectionFunctor G S).obj T) :
    sourceSliceHomToDependentSection G S X T
        (sourceDependentSectionHomToSlice G S X T f) =
      f := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext x
  apply SourceDependentSection.ext
  intro s
  change
    sourceDependentSectionHomToSliceFunction G S X T f
        (sourceActionProductMk G S X s x) =
      (show SourceDependentSection T from f.hom.hom x) s
  exact sourceDependentSectionHomToSliceFunction_mk G S X T f s x

/-- The explicit currying equivalence for product with an arbitrary finite
continuous base action. -/
noncomputable def sourceSliceDependentSectionHomEquiv
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G)
    (T : Over S) :
    ((sourceSliceProductFunctor G S).obj X ⟶ T) ≃
      (X ⟶ (sourceDependentSectionFunctor G S).obj T) where
  toFun := sourceSliceHomToDependentSection G S X T
  invFun := sourceDependentSectionHomToSlice G S X T
  left_inv := sourceSliceDependentSection_leftInverse G S X T
  right_inv := sourceSliceDependentSection_rightInverse G S X T

/-- Composition of morphisms of continuous actions is ordinary composition
on underlying points. -/
theorem sourceContinuousAction_comp_apply
    {G : ProfiniteGrp.{u}}
    {X Y Z : ContAction FintypeCat.{u} G}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.obj.V) :
    (f ≫ g).hom.hom x = g.hom.hom (f.hom.hom x) := by
  have hmap :=
    Functor.map_comp (continuousActionFiber G) f g
  have hpoint :=
    ConcreteCategory.congr_hom hmap x
  simpa only [FintypeCat.comp_apply] using hpoint

/-- On left objects, the slice product functor maps `f` by
`id_S x f`. -/
theorem sourceSliceProduct_map_left
    (G : ProfiniteGrp.{u})
    (S : ContAction FintypeCat.{u} G)
    {X Y : ContAction FintypeCat.{u} G}
    (f : X ⟶ Y) :
    ((sourceSliceProductFunctor G S).map f).left =
      prod.map (𝟙 S) f := by
  dsimp only [sourceSliceProductFunctor]
  rfl

/-- The map `id_S x f` sends the explicit pair `(s,x)` to `(s,f(x))`. -/
theorem sourceSliceProduct_map_mk
    (G : ProfiniteGrp.{u})
    (S : ContAction FintypeCat.{u} G)
    {X Y : ContAction FintypeCat.{u} G}
    (f : X ⟶ Y) (s : S.obj.V) (x : X.obj.V) :
    ((sourceSliceProductFunctor G S).map f).left.hom.hom
        (sourceActionProductMk G S X s x) =
      sourceActionProductMk G S Y s (f.hom.hom x) := by
  let point :=
    sourceActionProductMk G S X s x
  apply (sourceActionProductEquiv G S Y).injective
  rw [sourceActionProductEquiv_mk]
  apply Prod.ext
  · change
      (sourceActionProductEquiv G S Y
        (((sourceSliceProductFunctor G S).map f).left.hom.hom
          (sourceActionProductMk G S X s x))).1 = s
    rw [sourceActionProductEquiv_fst]
    have hfirst :
        ((sourceSliceProductFunctor G S).map f).left ≫
            (prod.fst : S ⨯ Y ⟶ S) =
          (prod.fst : S ⨯ X ⟶ S) := by
      rw [sourceSliceProduct_map_left]
      exact (prod.map_fst (𝟙 S) f).trans (Category.comp_id _)
    let mappedPoint :=
      ((sourceSliceProductFunctor G S).map f).left.hom.hom point
    calc
      (prod.fst : S ⨯ Y ⟶ S).hom.hom mappedPoint =
          (((sourceSliceProductFunctor G S).map f).left ≫
            (prod.fst : S ⨯ Y ⟶ S)).hom.hom point :=
        (sourceContinuousAction_comp_apply
          ((sourceSliceProductFunctor G S).map f).left
          (prod.fst : S ⨯ Y ⟶ S) point).symm
      _ =
          (prod.fst : S ⨯ X ⟶ S).hom.hom point := by
        exact congrArg
          (fun map : (S ⨯ X) ⟶ S => map.hom.hom point)
          hfirst
      _ = s := sourceActionProductMk_fst G S X s x
  · change
      (sourceActionProductEquiv G S Y
        (((sourceSliceProductFunctor G S).map f).left.hom.hom
          (sourceActionProductMk G S X s x))).2 =
        f.hom.hom x
    rw [sourceActionProductEquiv_snd]
    have hsecond :
        ((sourceSliceProductFunctor G S).map f).left ≫
            (prod.snd : S ⨯ Y ⟶ Y) =
          (prod.snd : S ⨯ X ⟶ X) ≫ f := by
      rw [sourceSliceProduct_map_left]
      exact prod.map_snd (𝟙 S) f
    let mappedPoint :=
      ((sourceSliceProductFunctor G S).map f).left.hom.hom point
    calc
      (prod.snd : S ⨯ Y ⟶ Y).hom.hom mappedPoint =
          (((sourceSliceProductFunctor G S).map f).left ≫
            (prod.snd : S ⨯ Y ⟶ Y)).hom.hom point :=
        (sourceContinuousAction_comp_apply
          ((sourceSliceProductFunctor G S).map f).left
          (prod.snd : S ⨯ Y ⟶ Y) point).symm
      _ =
          ((prod.snd : S ⨯ X ⟶ X) ≫ f).hom.hom point := by
        exact congrArg
          (fun map : (S ⨯ X) ⟶ Y => map.hom.hom point)
          hsecond
      _ =
          f.hom.hom
            ((prod.snd : S ⨯ X ⟶ X).hom.hom point) :=
        sourceContinuousAction_comp_apply
          (prod.snd : S ⨯ X ⟶ X) f point
      _ = f.hom.hom x := by
        dsimp only [point]
        rw [sourceActionProductMk_snd]

/-- Naturality of uncurrying in the action variable. -/
theorem sourceSliceDependentSection_naturality_left_symm
    (G : ProfiniteGrp.{u})
    (S : ContAction FintypeCat.{u} G)
    {X' X : ContAction FintypeCat.{u} G}
    (T : Over S)
    (f : X' ⟶ X)
    (g : X ⟶ (sourceDependentSectionFunctor G S).obj T) :
    (sourceSliceDependentSectionHomEquiv G S X' T).symm (f ≫ g) =
      (sourceSliceProductFunctor G S).map f ≫
        (sourceSliceDependentSectionHomEquiv G S X T).symm g := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext point
  let coordinates :=
    sourceActionProductEquiv G S X' point
  have hpoint :
      sourceActionProductMk G S X'
          coordinates.1 coordinates.2 =
        point :=
    (sourceActionProductEquiv G S X').symm_apply_apply point
  rw [← hpoint]
  change
    sourceDependentSectionHomToSliceFunction G S X' T (f ≫ g)
        (sourceActionProductMk G S X'
          coordinates.1 coordinates.2) =
      (((sourceSliceProductFunctor G S).map f).left ≫
        (sourceDependentSectionHomToSlice G S X T g).left).hom.hom
          (sourceActionProductMk G S X'
            coordinates.1 coordinates.2)
  calc
    sourceDependentSectionHomToSliceFunction G S X' T (f ≫ g)
          (sourceActionProductMk G S X'
            coordinates.1 coordinates.2) =
        (show SourceDependentSection T from
          (f ≫ g).hom.hom coordinates.2) coordinates.1 :=
      sourceDependentSectionHomToSliceFunction_mk
        G S X' T (f ≫ g) coordinates.1 coordinates.2
    _ =
        (show SourceDependentSection T from
          g.hom.hom (f.hom.hom coordinates.2)) coordinates.1 := by
      rw [sourceContinuousAction_comp_apply f g coordinates.2]
    _ =
        sourceDependentSectionHomToSliceFunction G S X T g
          (sourceActionProductMk G S X coordinates.1
            (f.hom.hom coordinates.2)) :=
      (sourceDependentSectionHomToSliceFunction_mk
        G S X T g coordinates.1
          (f.hom.hom coordinates.2)).symm
    _ =
        sourceDependentSectionHomToSliceFunction G S X T g
          (((sourceSliceProductFunctor G S).map f).left.hom.hom
            (sourceActionProductMk G S X'
              coordinates.1 coordinates.2)) := by
      rw [sourceSliceProduct_map_mk]
    _ =
        (((sourceSliceProductFunctor G S).map f).left ≫
          (sourceDependentSectionHomToSlice G S X T g).left).hom.hom
            (sourceActionProductMk G S X'
              coordinates.1 coordinates.2) := by
      exact
        (sourceContinuousAction_comp_apply
          ((sourceSliceProductFunctor G S).map f).left
          (sourceDependentSectionHomToSlice G S X T g).left
          (sourceActionProductMk G S X'
            coordinates.1 coordinates.2)).symm

/-- Naturality of currying in the slice variable. -/
theorem sourceSliceDependentSection_naturality_right
    (G : ProfiniteGrp.{u})
    (S X : ContAction FintypeCat.{u} G)
    {T U : Over S}
    (f : (sourceSliceProductFunctor G S).obj X ⟶ T)
    (g : T ⟶ U) :
    sourceSliceDependentSectionHomEquiv G S X U (f ≫ g) =
      sourceSliceDependentSectionHomEquiv G S X T f ≫
        (sourceDependentSectionFunctor G S).map g := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext x
  apply SourceDependentSection.ext
  intro s
  change
    (f.left ≫ g.left).hom.hom
        (sourceActionProductMk G S X s x) =
      g.left.hom.hom
        (f.left.hom.hom
          (sourceActionProductMk G S X s x))
  exact sourceContinuousAction_comp_apply f.left g.left
    (sourceActionProductMk G S X s x)

/-- Product with an arbitrary finite continuous `G`-set is left adjoint to
the action of dependent sections. -/
noncomputable def sourceSliceProductAdjDependentSection
    (G : ProfiniteGrp.{u})
    (S : ContAction FintypeCat.{u} G) :
    sourceSliceProductFunctor G S ⊣
      sourceDependentSectionFunctor G S :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sourceSliceDependentSectionHomEquiv G S
      homEquiv_naturality_left_symm :=
        fun f g =>
          sourceSliceDependentSection_naturality_left_symm
            G S _ f g
      homEquiv_naturality_right :=
        fun f g =>
          sourceSliceDependentSection_naturality_right
            G S _ f g }

/-- Proposition 1.2.1(iii) of *The Geometry of Anabelioids*: product with
any object `S` preserves finite colimits.  Together with finite-limit
preservation above, this is the exactness of `i_S^*`. -/
noncomputable instance sourceSliceProduct_preservesFiniteColimits
    (G : ProfiniteGrp.{u})
    (S : ContAction FintypeCat.{u} G) :
    Limits.PreservesFiniteColimits
      (sourceSliceProductFunctor G S) := by
  letI :=
    (sourceSliceProductAdjDependentSection G S).leftAdjoint_preservesColimits
  infer_instance

/-! ## Induction as the extension functor -/

/-- The continuous inclusion of an open subgroup into its ambient profinite
group. -/
def sourceOpenSubgroupInclusion
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    H →ₜ* G where
  toMonoidHom := H.toSubgroup.subtype
  continuous_toFun := continuous_subtype_val

/-- Restriction of a finite continuous `G`-action to the open subgroup `H`. -/
noncomputable def sourceOpenSubgroupRestriction
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    ContAction FintypeCat.{u} G ⥤ ContAction FintypeCat.{u} H :=
  ContAction.res FintypeCat (sourceOpenSubgroupInclusion G H)

/-- The extension functor underlying `j_{G/H}` after the slice is identified
with `B(H)`. -/
noncomputable def sourceOpenSubgroupInduction
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    ContAction FintypeCat.{u} H ⥤ ContAction FintypeCat.{u} G :=
  sourceInductionToSlice G H ⋙ Over.forget (sourceOpenCosetAction G H)

/-- Restrict an equivariant map out of an induced action along the classes
`[1,t]`. -/
noncomputable def sourceInductionHomToRestriction
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (X : ContAction FintypeCat.{u} G)
    (f : (sourceOpenSubgroupInduction G H).obj T ⟶ X) :
    T ⟶ (sourceOpenSubgroupRestriction G H).obj X := by
  apply ObjectProperty.homMk
  refine
    ({ hom :=
        FintypeCat.homMk
          (fun t =>
            f.hom.hom
              (SourceInducedSet.mk
                G H.toSubgroup T.obj.V 1 t))
       comm := fun h => by
         ext t
         have hinduced :
             SourceInducedSet.mk G H.toSubgroup T.obj.V 1 (h • t) =
               (h : G) •
                 SourceInducedSet.mk
                   G H.toSubgroup T.obj.V 1 t := by
           rw [SourceInducedSet.smul_mk, mul_one]
           simpa using
             (SourceInducedSet.mk_eq_mk
               G H.toSubgroup T.obj.V 1 (h • t) h).symm
         change
           f.hom.hom
               (SourceInducedSet.mk
                 G H.toSubgroup T.obj.V 1 (h • t)) =
             (h : G) •
               f.hom.hom
                 (SourceInducedSet.mk
                   G H.toSubgroup T.obj.V 1 t)
         rw [hinduced]
         exact
           ConcreteCategory.congr_hom
             (f.hom.comm (h : G))
             (SourceInducedSet.mk
               G H.toSubgroup T.obj.V 1 t) } :
      T.obj ⟶
        ((sourceOpenSubgroupRestriction G H).obj X).obj)

/-- The function `[g,t] |-> g.f(t)` extending an `H`-equivariant map to a
`G`-equivariant map out of the induced action. -/
noncomputable def sourceRestrictionHomToInductionFunction
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (X : ContAction FintypeCat.{u} G)
    (f : T ⟶ (sourceOpenSubgroupRestriction G H).obj X) :
    SourceInducedSet G H.toSubgroup T.obj.V → X.obj.V :=
  Quotient.lift
    (fun p : G × T.obj.V =>
      p.1 • (show X.obj.V from f.hom.hom p.2))
    (by
      rintro a b ⟨h, hb1, hb2⟩
      change
        a.1 • (show X.obj.V from f.hom.hom a.2) =
          b.1 • (show X.obj.V from f.hom.hom b.2)
      rw [hb1, hb2]
      have hequivariant :=
        sourceContinuousActionMap_equivariant H f h⁻¹ a.2
      rw [hequivariant]
      change
        a.1 • (show X.obj.V from f.hom.hom a.2) =
          (a.1 * (h : G)) •
            (((h⁻¹ : H) : G) •
              (show X.obj.V from f.hom.hom a.2))
      rw [← mul_smul, Subgroup.coe_inv, mul_inv_cancel_right])

@[simp]
theorem sourceRestrictionHomToInductionFunction_mk
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (X : ContAction FintypeCat.{u} G)
    (f : T ⟶ (sourceOpenSubgroupRestriction G H).obj X)
    (g : G) (t : T.obj.V) :
    sourceRestrictionHomToInductionFunction G H T X f
        (SourceInducedSet.mk G H.toSubgroup T.obj.V g t) =
      g • (show X.obj.V from f.hom.hom t) :=
  rfl

/-- Extend an `H`-equivariant map by the source formula
`[g,t] |-> g.f(t)`. -/
noncomputable def sourceRestrictionHomToInduction
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (X : ContAction FintypeCat.{u} G)
    (f : T ⟶ (sourceOpenSubgroupRestriction G H).obj X) :
    (sourceOpenSubgroupInduction G H).obj T ⟶ X := by
  apply ObjectProperty.homMk
  refine
    ({ hom :=
        FintypeCat.homMk
          (sourceRestrictionHomToInductionFunction G H T X f)
       comm := fun g => by
         ext q
         induction q using Quotient.inductionOn with
         | _ p =>
             change
               (g * p.1) •
                   (show X.obj.V from f.hom.hom p.2) =
                 g •
                   (p.1 • (show X.obj.V from f.hom.hom p.2))
             exact
               mul_smul g p.1
                 (show X.obj.V from f.hom.hom p.2) } :
      ((sourceOpenSubgroupInduction G H).obj T).obj ⟶ X.obj)

/-- Extending a restricted map and then evaluating it on `[1,t]` recovers
the original `H`-equivariant map. -/
theorem sourceInductionRestriction_rightInverse
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (X : ContAction FintypeCat.{u} G)
    (f : T ⟶ (sourceOpenSubgroupRestriction G H).obj X) :
    sourceInductionHomToRestriction G H T X
        (sourceRestrictionHomToInduction G H T X f) =
      f := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext t
  change (1 : G) • (show X.obj.V from f.hom.hom t) =
    f.hom.hom t
  exact one_smul G (show X.obj.V from f.hom.hom t)

/-- Restricting a map out of induction and extending it by
`[g,t] |-> g.f([1,t])` recovers the original `G`-equivariant map. -/
theorem sourceInductionRestriction_leftInverse
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (X : ContAction FintypeCat.{u} G)
    (f : (sourceOpenSubgroupInduction G H).obj T ⟶ X) :
    sourceRestrictionHomToInduction G H T X
        (sourceInductionHomToRestriction G H T X f) =
      f := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext q
  induction q using Quotient.inductionOn with
  | _ p =>
      change
        p.1 •
            f.hom.hom
              (SourceInducedSet.mk
                G H.toSubgroup T.obj.V 1 p.2) =
          f.hom.hom
            (SourceInducedSet.mk
              G H.toSubgroup T.obj.V p.1 p.2)
      calc
        p.1 •
              f.hom.hom
                (SourceInducedSet.mk
                  G H.toSubgroup T.obj.V 1 p.2) =
            f.hom.hom
              (p.1 •
                SourceInducedSet.mk
                  G H.toSubgroup T.obj.V 1 p.2) := by
              exact
                (ConcreteCategory.congr_hom
                  (f.hom.comm p.1)
                  (SourceInducedSet.mk
                    G H.toSubgroup T.obj.V 1 p.2)).symm
        _ =
            f.hom.hom
              (SourceInducedSet.mk
                G H.toSubgroup T.obj.V p.1 p.2) := by
              rw [SourceInducedSet.smul_mk, mul_one]

/-- The explicit induction/restriction bijection on equivariant Hom sets. -/
noncomputable def sourceInductionRestrictionHomEquiv
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    (X : ContAction FintypeCat.{u} G) :
    ((sourceOpenSubgroupInduction G H).obj T ⟶ X) ≃
      (T ⟶ (sourceOpenSubgroupRestriction G H).obj X) where
  toFun := sourceInductionHomToRestriction G H T X
  invFun := sourceRestrictionHomToInduction G H T X
  left_inv := sourceInductionRestriction_leftInverse G H T X
  right_inv := sourceInductionRestriction_rightInverse G H T X

/-- Naturality of the inverse induction/restriction Hom map in the
`H`-action. -/
theorem sourceInductionRestriction_naturality_left_symm
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    {T U : ContAction FintypeCat.{u} H}
    (X : ContAction FintypeCat.{u} G)
    (f : T ⟶ U)
    (g : U ⟶ (sourceOpenSubgroupRestriction G H).obj X) :
    (sourceInductionRestrictionHomEquiv G H T X).symm (f ≫ g) =
      (sourceOpenSubgroupInduction G H).map f ≫
        (sourceInductionRestrictionHomEquiv G H U X).symm g := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext q
  induction q using Quotient.inductionOn with
  | _ p => rfl

/-- Naturality of the induction/restriction Hom map in the `G`-action. -/
theorem sourceInductionRestriction_naturality_right
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G)
    (T : ContAction FintypeCat.{u} H)
    {X Y : ContAction FintypeCat.{u} G}
    (f : (sourceOpenSubgroupInduction G H).obj T ⟶ X)
    (g : X ⟶ Y) :
    sourceInductionRestrictionHomEquiv G H T Y (f ≫ g) =
      sourceInductionRestrictionHomEquiv G H T X f ≫
        (sourceOpenSubgroupRestriction G H).map g := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext t
  rfl

/-- The source extension formula gives the induction-restriction
adjunction for the open subgroup `H ≤ G`. -/
noncomputable def sourceInductionRestrictionAdjunction
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    sourceOpenSubgroupInduction G H ⊣
      sourceOpenSubgroupRestriction G H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sourceInductionRestrictionHomEquiv G H
      homEquiv_naturality_left_symm :=
        fun f g =>
          sourceInductionRestriction_naturality_left_symm G H _ f g
      homEquiv_naturality_right :=
        fun f g =>
          sourceInductionRestriction_naturality_right G H _ f g }

/-- Transporting the slice adjunction through `B(H) ≃ B(G)_{G/H}` gives
another right adjoint to open-subgroup induction. -/
noncomputable def sourceSliceTransportedAdjunction
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    sourceOpenSubgroupInduction G H ⊣
      sourceSliceProductFunctor G (sourceOpenCosetAction G H) ⋙
        sourceSliceFiberFunctor G H :=
  (sourceOpenCosetSliceEquivalence G H).toAdjunction.comp
    (sourceSliceForgetAdjProduct G (sourceOpenCosetAction G H))

/-- Under the source equivalence `B(H) ≃ B(G)_{G/H}`, product with `G/H`
is naturally isomorphic to restriction from `G` to `H`. -/
noncomputable def sourceOpenSubgroupRestrictionSliceIso
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    sourceOpenSubgroupRestriction G H ≅
      sourceSliceProductFunctor G (sourceOpenCosetAction G H) ⋙
        sourceSliceFiberFunctor G H :=
  (sourceInductionRestrictionAdjunction G H).rightAdjointUniq
    (sourceSliceTransportedAdjunction G H)

/-- Definition 1.2.2(i), expressed on the contravariant pullback functor:
`pullback : X → Y` is finite etale when `Y` is equivalent to a slice `X_S`
and `pullback` is product with `S`, followed by that equivalence. -/
structure SourceFiniteEtaleFunctorFactorization
    {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{v'} D]
    [Limits.HasBinaryProducts C]
    (pullback : C ⥤ D) where
  object : C
  sliceEquivalence : D ≌ Over object
  pullbackIso :
    pullback ≅ Over.star object ⋙ sliceEquivalence.inverse

/-- The restriction functor attached to an open subgroup has the
choice-independent finite-etale factorization through the coset slice. -/
noncomputable def sourceOpenSubgroupFiniteEtaleFactorization
    (G : ProfiniteGrp.{u}) (H : OpenSubgroup G) :
    SourceFiniteEtaleFunctorFactorization
      (sourceOpenSubgroupRestriction G H) where
  object := sourceOpenCosetAction G H
  sliceEquivalence := sourceOpenCosetSliceEquivalence G H
  pullbackIso := sourceOpenSubgroupRestrictionSliceIso G H

end Iut
