import LeanFormal.IUT.IUTII.Kummer.ContinuousKummerGerm
import Mathlib.Topology.Algebra.MulAction

/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
  The canonical continuous Kummer germ on every element of a divisible
  commutative group.

  A continuous action on a discrete coefficient group gives an open
  stabilizer for each element.  Compatible rational roots then define the
  single-element germ from `ContinuousKummerGerm`.  The proofs below compare
  different open stabilizers on their intersection and compare product root
  systems explicitly.  Consequently the construction is a genuine group
  homomorphism, rather than a family of unrelated classes.

  This is the group-cohomological side of IUT II, Example 1.8.  No
  Frobenioid evaluation or group/Frobenioid comparison is asserted here.
-/

namespace LeanFormal.IUT

universe u

namespace DiscreteContinuousGroupAction

variable
  {G B : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup B] [TopologicalSpace B] [DiscreteTopology B]

@[implicit_reducible]
protected def toMulAction
    (action : DiscreteContinuousGroupAction G B) : MulAction G B where
  smul := action.act
  one_smul := action.act_one_group
  mul_smul := action.act_mul_group

protected theorem toContinuousSMul
    (action : DiscreteContinuousGroupAction G B) :
    letI := action.toMulAction
    ContinuousSMul G B := by
  letI := action.toMulAction
  exact ⟨action.continuous_action⟩

def stabilizer
    (action : DiscreteContinuousGroupAction G B) (value : B) :
    OpenSubgroup G := by
  letI := action.toMulAction
  letI : ContinuousSMul G B := action.toContinuousSMul
  exact
    { toSubgroup := MulAction.stabilizer G value
      isOpen' := stabilizer_isOpen G value }

@[simp] theorem mem_stabilizer_iff
    (action : DiscreteContinuousGroupAction G B)
    (value : B) (g : G) :
    g ∈ action.stabilizer value ↔ action.act g value = value := by
  letI := action.toMulAction
  exact MulAction.mem_stabilizer_iff

theorem stabilizer_fixed
    (action : DiscreteContinuousGroupAction G B)
    (value : B) (g : action.stabilizer value) :
    action.act (g : G) value = value :=
  (action.mem_stabilizer_iff value g).mp g.2

end DiscreteContinuousGroupAction

namespace CompatibleRootSystem

variable {B : Type u} [CommGroup B]

def mul
    {firstValue secondValue : B}
    (first : CompatibleRootSystem B firstValue)
    (second : CompatibleRootSystem B secondValue) :
    CompatibleRootSystem B (firstValue * secondValue) where
  roots := first.roots + second.roots
  root_one := by
    apply Additive.toMul.injective
    change
      (first.roots 1).toMul * (second.roots 1).toMul =
        firstValue * secondValue
    rw [congrArg Additive.toMul first.root_one,
      congrArg Additive.toMul second.root_one]
    rfl

@[simp] theorem mul_roots
    {firstValue secondValue : B}
    (first : CompatibleRootSystem B firstValue)
    (second : CompatibleRootSystem B secondValue)
    (q : ℚ) :
    ((first.mul second).roots q).toMul =
      (first.roots q).toMul * (second.roots q).toMul :=
  rfl

end CompatibleRootSystem

namespace UnitKummerRootRealization

variable
  {G B : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  {action : DiscreteContinuousGroupAction G B}

theorem representatives_equivalent_of_common_value
    {firstSubgroup secondSubgroup : OpenSubgroup G}
    {value : B}
    (first : UnitKummerRootRealization action firstSubgroup value)
    (second : UnitKummerRootRealization action secondSubgroup value) :
    first.representative.Equivalent second.representative := by
  refine
    ⟨firstSubgroup ⊓ secondSubgroup, inf_le_left, inf_le_right,
      rootDifference first.rootSystem second.rootSystem, ?_⟩
  intro g
  apply MonoidHom.ext
  intro circle
  let additiveCircle : AddCircle (1 : ℚ) := circle.toAdd
  change
    second.ratioCyclotome
          ⟨(g : G), g.2.2⟩
          (Multiplicative.ofAdd additiveCircle) =
      (rootDifference first.rootSystem second.rootSystem)⁻¹
            (Multiplicative.ofAdd additiveCircle) *
        first.ratioCyclotome
            ⟨(g : G), g.2.1⟩
            (Multiplicative.ofAdd additiveCircle) *
        (KummerCyclotome.continuousAction action).act (g : G)
          (rootDifference first.rootSystem second.rootSystem)
          (Multiplicative.ofAdd additiveCircle)
  induction additiveCircle using Quotient.inductionOn with
  | _ q =>
      change
        action.act (g : G) (second.rootSystem.roots q).toMul /
              (second.rootSystem.roots q).toMul =
          ((second.rootSystem.roots q).toMul /
              (first.rootSystem.roots q).toMul)⁻¹ *
            (action.act (g : G) (first.rootSystem.roots q).toMul /
              (first.rootSystem.roots q).toMul) *
            action.act (g : G)
              ((second.rootSystem.roots q).toMul /
                (first.rootSystem.roots q).toMul)
      rw [action.act_div]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel

theorem germ_eq_of_common_value
    {firstSubgroup secondSubgroup : OpenSubgroup G}
    {value : B}
    (first : UnitKummerRootRealization action firstSubgroup value)
    (second : UnitKummerRootRealization action secondSubgroup value) :
    first.germ = second.germ := by
  apply Quotient.sound
  exact representatives_equivalent_of_common_value first second

def mul
    {firstSubgroup secondSubgroup : OpenSubgroup G}
    {firstValue secondValue : B}
    (first : UnitKummerRootRealization action firstSubgroup firstValue)
    (second : UnitKummerRootRealization action secondSubgroup secondValue) :
    UnitKummerRootRealization action
      (firstSubgroup ⊓ secondSubgroup) (firstValue * secondValue) where
  fixed := by
    intro g
    rw [action.act_mul, first.fixed ⟨g, g.2.1⟩,
      second.fixed ⟨g, g.2.2⟩]
  rootSystem := first.rootSystem.mul second.rootSystem

theorem mul_ratioUnit
    {firstSubgroup secondSubgroup : OpenSubgroup G}
    {firstValue secondValue : B}
    (first : UnitKummerRootRealization action firstSubgroup firstValue)
    (second : UnitKummerRootRealization action secondSubgroup secondValue)
    (g : ↥(firstSubgroup ⊓ secondSubgroup)) (q : ℚ) :
    (first.mul second).ratioUnit g q =
      first.ratioUnit ⟨g, g.2.1⟩ q *
        second.ratioUnit ⟨g, g.2.2⟩ q := by
  simp only [ratioUnit, mul, CompatibleRootSystem.mul_roots,
    action.act_mul, div_eq_mul_inv, mul_inv_rev]
  ac_rfl

theorem mul_germ
    {firstSubgroup secondSubgroup : OpenSubgroup G}
    {firstValue secondValue : B}
    (first : UnitKummerRootRealization action firstSubgroup firstValue)
    (second : UnitKummerRootRealization action secondSubgroup secondValue) :
    (first.mul second).germ = first.germ * second.germ := by
  apply Quotient.sound
  refine
    Iut.ContinuousH1GermRepresentative.Equivalent.of_equal_on
      (firstSubgroup ⊓ secondSubgroup) le_rfl le_rfl ?_
  intro g
  apply MonoidHom.ext
  intro circle
  let additiveCircle : AddCircle (1 : ℚ) := circle.toAdd
  change
    first.ratioCyclotome
          ⟨(g : G), g.2.1⟩
          (Multiplicative.ofAdd additiveCircle) *
        second.ratioCyclotome
          ⟨(g : G), g.2.2⟩
          (Multiplicative.ofAdd additiveCircle) =
      (first.mul second).ratioCyclotome g
        (Multiplicative.ofAdd additiveCircle)
  induction additiveCircle using Quotient.inductionOn with
  | _ q => exact (first.mul_ratioUnit second g q).symm

end UnitKummerRootRealization

namespace CanonicalKummerMap

variable
  {G B : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [RootableBy B ℕ]

noncomputable def realization
    (action : DiscreteContinuousGroupAction G B) (value : B) :
    UnitKummerRootRealization action (action.stabilizer value) value :=
  UnitKummerRootRealization.ofRootable action
    (action.stabilizer value) value (action.stabilizer_fixed value)

noncomputable def germ
    (action : DiscreteContinuousGroupAction G B) (value : B) :
    Iut.ContinuousH1Germ (KummerCyclotome.continuousAction action) :=
  (realization action value).germ

theorem germ_mul
    (action : DiscreteContinuousGroupAction G B)
    (first second : B) :
    germ action (first * second) = germ action first * germ action second := by
  let productRealization :=
    (realization action first).mul (realization action second)
  calc
    germ action (first * second) = productRealization.germ :=
      UnitKummerRootRealization.germ_eq_of_common_value
        (realization action (first * second)) productRealization
    _ = germ action first * germ action second :=
      UnitKummerRootRealization.mul_germ
        (realization action first) (realization action second)

theorem germ_one
    (action : DiscreteContinuousGroupAction G B) :
    germ action 1 = 1 := by
  have productIdentity := germ_mul action (1 : B) 1
  have idempotent : germ action 1 = germ action 1 * germ action 1 := by
    simpa only [one_mul] using productIdentity
  have leftCancellable : germ action 1 * 1 = germ action 1 * germ action 1 := by
    simpa only [mul_one] using idempotent
  exact (mul_left_cancel leftCancellable).symm

noncomputable def hom
    (action : DiscreteContinuousGroupAction G B) :
    B →* Iut.ContinuousH1Germ
      (KummerCyclotome.continuousAction action) where
  toFun := germ action
  map_one' := germ_one action
  map_mul' := germ_mul action

@[simp] theorem hom_apply
    (action : DiscreteContinuousGroupAction G B) (value : B) :
    hom action value = germ action value :=
  rfl

end CanonicalKummerMap

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def canonicalContinuousKummerMap : Obligation :=
  { id := "IUT-II.canonical-continuous-kummer-map"
    source := "IUT II, Example 1.8(ii)-(iv); Definition 4.9(i), group-cohomological side"
    status := VerificationStatus.provedKernel
    note :=
      "Every element has an open stabilizer under a discrete continuous action. " ++
        "Its compatible rational roots define a root-choice and open-subgroup-independent " ++
        "continuous H1 germ. Product root systems prove that these germs form a genuine " ++
        "group homomorphism. Local absolute Galois continuity, Frobenioid evaluation, " ++
        "and the group/Frobenioid Kummer comparison remain separate obligations."
    dependsOn := ["IUT-II.continuous-unit-kummer-germ"] }

end LeanFormal.IUT.Audit
