/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import Iut.Foundations.ContinuousH1
import LeanFormal.IUT.IUTII.Kummer.RationalRootSystem
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace LeanFormal.IUT

/-!
  Continuous Kummer germs constructed from compatible rational roots.

  The construction follows the root-ratio and continuous-H1 portion of
  `promachina/iut-lean`, `SourceThetaEvaluation.lean`, upstream commit
  `3de1d7c1`, under Apache-2.0.  The coefficient cyclotome is the genuine
  group `Hom(Q/Z, B)` with its pointwise discrete topology.  Root ratios,
  their crossed-homomorphism law, continuity, and independence of the chosen
  compatible root system are derived below rather than stored as fields.
-/

universe u

structure DiscreteContinuousGroupAction
    (G B : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommGroup B] [TopologicalSpace B] [DiscreteTopology B] where
  automorphism : G →* MulAut B
  continuous_action : Continuous fun p : G × B => automorphism p.1 p.2

namespace DiscreteContinuousGroupAction

variable
  {G B : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup B] [TopologicalSpace B] [DiscreteTopology B]

def act (action : DiscreteContinuousGroupAction G B) (g : G) (b : B) : B :=
  action.automorphism g b

@[simp] theorem act_one_group
    (action : DiscreteContinuousGroupAction G B) (b : B) :
    action.act 1 b = b := by
  change action.automorphism 1 b = b
  rw [map_one]
  rfl

@[simp] theorem act_one
    (action : DiscreteContinuousGroupAction G B) (g : G) :
    action.act g 1 = 1 :=
  map_one (action.automorphism g)

@[simp] theorem act_mul_group
    (action : DiscreteContinuousGroupAction G B) (g h : G) (b : B) :
    action.act (g * h) b = action.act g (action.act h b) := by
  change action.automorphism (g * h) b =
    action.automorphism g (action.automorphism h b)
  rw [map_mul]
  rfl

@[simp] theorem act_mul
    (action : DiscreteContinuousGroupAction G B) (g : G) (a b : B) :
    action.act g (a * b) = action.act g a * action.act g b :=
  map_mul (action.automorphism g) a b

@[simp] theorem act_inv
    (action : DiscreteContinuousGroupAction G B) (g : G) (a : B) :
    action.act g a⁻¹ = (action.act g a)⁻¹ :=
  map_inv (action.automorphism g) a

@[simp] theorem act_div
    (action : DiscreteContinuousGroupAction G B) (g : G) (a b : B) :
    action.act g (a / b) = action.act g a / action.act g b :=
  map_div (action.automorphism g) a b

end DiscreteContinuousGroupAction

abbrev KummerCyclotome (B : Type u) [CommGroup B] : Type u :=
  Multiplicative (AddCircle (1 : ℚ)) →* B

namespace KummerCyclotome

variable
  {G B : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup B] [TopologicalSpace B] [DiscreteTopology B]

def coeFunctionMonoidHom :
    KummerCyclotome B →* (Multiplicative (AddCircle (1 : ℚ)) → B) where
  toFun hom := hom
  map_one' := rfl
  map_mul' _ _ := rfl

@[implicit_reducible]
noncomputable def topology : TopologicalSpace (KummerCyclotome B) := by
  exact TopologicalSpace.induced coeFunctionMonoidHom inferInstance

noncomputable instance instTopologicalSpace :
    TopologicalSpace (KummerCyclotome B) := topology

noncomputable instance instIsTopologicalGroup :
    IsTopologicalGroup (KummerCyclotome B) :=
  topologicalGroup_induced coeFunctionMonoidHom

omit [DiscreteTopology B] in
theorem continuous_iff_eval_discrete
    {X : Type u} [TopologicalSpace X]
    (f : X → KummerCyclotome B) :
    Continuous f ↔
      ∀ q : Multiplicative (AddCircle (1 : ℚ)),
        Continuous fun x => f x q := by
  change @Continuous X (KummerCyclotome B) _ topology f ↔ _
  rw [topology, continuous_induced_rng, continuous_pi_iff]
  rfl

omit [DiscreteTopology B] in
theorem continuous_eval_discrete
    (q : Multiplicative (AddCircle (1 : ℚ))) :
    Continuous fun cyclotome : KummerCyclotome B => cyclotome q :=
  (continuous_iff_eval_discrete (B := B) id).mp continuous_id q

noncomputable def mapAut
    (action : DiscreteContinuousGroupAction G B) (g : G) :
    MulAut (KummerCyclotome B) where
  toFun cyclotome :=
    (action.automorphism g).toMonoidHom.comp cyclotome
  invFun cyclotome :=
    (action.automorphism g).symm.toMonoidHom.comp cyclotome
  left_inv cyclotome := by
    apply MonoidHom.ext
    intro q
    exact (action.automorphism g).symm_apply_apply (cyclotome q)
  right_inv cyclotome := by
    apply MonoidHom.ext
    intro q
    exact (action.automorphism g).apply_symm_apply (cyclotome q)
  map_mul' first second := by
    apply MonoidHom.ext
    intro q
    exact map_mul (action.automorphism g) (first q) (second q)

noncomputable def actionHom
    (action : DiscreteContinuousGroupAction G B) :
    G →* MulAut (KummerCyclotome B) where
  toFun := mapAut action
  map_one' := by
    apply MulEquiv.ext
    intro cyclotome
    apply MonoidHom.ext
    intro q
    change action.automorphism 1 (cyclotome q) = cyclotome q
    rw [map_one]
    rfl
  map_mul' first second := by
    apply MulEquiv.ext
    intro cyclotome
    apply MonoidHom.ext
    intro q
    change action.automorphism (first * second) (cyclotome q) =
      action.automorphism first (action.automorphism second (cyclotome q))
    rw [map_mul]
    rfl

noncomputable def continuousAction
    (action : DiscreteContinuousGroupAction G B) :
    Iut.ContinuousGroupAction G (KummerCyclotome B) where
  automorphism := actionHom action
  continuous_action := by
    rw [continuous_iff_eval_discrete]
    intro q
    exact action.continuous_action.comp
      (continuous_fst.prodMk
        ((continuous_eval_discrete (B := B) q).comp continuous_snd))

@[simp] theorem continuousAction_act_apply
    (action : DiscreteContinuousGroupAction G B)
    (g : G) (cyclotome : KummerCyclotome B)
    (q : Multiplicative (AddCircle (1 : ℚ))) :
    (continuousAction action).act g cyclotome q =
      action.act g (cyclotome q) :=
  rfl

end KummerCyclotome

structure UnitKummerRootRealization
    {G B : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    (action : DiscreteContinuousGroupAction G B)
    (subgroup : OpenSubgroup G)
    (value : B) where
  fixed : ∀ g : subgroup, action.act (g : G) value = value
  rootSystem : CompatibleRootSystem B value

namespace UnitKummerRootRealization

variable
  {G B : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  {action : DiscreteContinuousGroupAction G B}
  {subgroup : OpenSubgroup G}
  {value : B}

noncomputable def ofRootable
    [RootableBy B ℕ]
    (action : DiscreteContinuousGroupAction G B)
    (subgroup : OpenSubgroup G)
    (value : B)
    (fixed : ∀ g : subgroup, action.act (g : G) value = value) :
    UnitKummerRootRealization action subgroup value where
  fixed := fixed
  rootSystem := CompatibleRootSystem.ofRootable value

def ratioUnit
    (realization : UnitKummerRootRealization action subgroup value)
    (g : subgroup) (q : ℚ) : B :=
  action.act (g : G) (realization.rootSystem.roots q).toMul /
    (realization.rootSystem.roots q).toMul

theorem ratioUnit_zero
    (realization : UnitKummerRootRealization action subgroup value)
    (g : subgroup) : realization.ratioUnit g 0 = 1 := by
  simp [ratioUnit]

theorem ratioUnit_add
    (realization : UnitKummerRootRealization action subgroup value)
    (g : subgroup) (first second : ℚ) :
    realization.ratioUnit g (first + second) =
      realization.ratioUnit g first * realization.ratioUnit g second := by
  have rootsAdd := congrArg Additive.toMul
    (realization.rootSystem.roots.map_add first second)
  change (realization.rootSystem.roots (first + second)).toMul =
    (realization.rootSystem.roots first).toMul *
      (realization.rootSystem.roots second).toMul at rootsAdd
  simp only [ratioUnit, rootsAdd, action.act_mul, div_eq_mul_inv,
    mul_inv_rev]
  ac_rfl

def ratioAddHom
    (realization : UnitKummerRootRealization action subgroup value)
    (g : subgroup) : ℚ →+ Additive B where
  toFun q := Additive.ofMul (realization.ratioUnit g q)
  map_zero' := congrArg Additive.ofMul (realization.ratioUnit_zero g)
  map_add' first second :=
    congrArg Additive.ofMul (realization.ratioUnit_add g first second)

theorem ratioUnit_one
    (realization : UnitKummerRootRealization action subgroup value)
    (g : subgroup) : realization.ratioUnit g 1 = 1 := by
  have rootOne := congrArg Additive.toMul realization.rootSystem.root_one
  change (realization.rootSystem.roots 1).toMul = value at rootOne
  simp [ratioUnit, rootOne, realization.fixed g]

theorem zmultiples_le_ratioAddHom_ker
    (realization : UnitKummerRootRealization action subgroup value)
    (g : subgroup) :
    AddSubgroup.zmultiples (1 : ℚ) ≤ (realization.ratioAddHom g).ker := by
  rw [AddSubgroup.zmultiples_le]
  change realization.ratioAddHom g 1 = 0
  apply Additive.toMul.injective
  exact realization.ratioUnit_one g

def ratioCyclotome
    (realization : UnitKummerRootRealization action subgroup value)
    (g : subgroup) : KummerCyclotome B :=
  AddMonoidHom.toMultiplicativeLeft
    (QuotientAddGroup.lift
      (AddSubgroup.zmultiples (1 : ℚ))
      (realization.ratioAddHom g)
      (realization.zmultiples_le_ratioAddHom_ker g))

@[simp] theorem ratioCyclotome_mk
    (realization : UnitKummerRootRealization action subgroup value)
    (g : subgroup) (q : ℚ) :
    realization.ratioCyclotome g
      (Multiplicative.ofAdd (q : AddCircle (1 : ℚ))) =
        realization.ratioUnit g q :=
  rfl

theorem ratioUnit_mul_group
    (realization : UnitKummerRootRealization action subgroup value)
    (first second : subgroup) (q : ℚ) :
    realization.ratioUnit (first * second) q =
      realization.ratioUnit first q *
        action.act (first : G) (realization.ratioUnit second q) := by
  let root := (realization.rootSystem.roots q).toMul
  change
    action.act ((first : G) * (second : G)) root / root =
      (action.act (first : G) root / root) *
        action.act (first : G)
          (action.act (second : G) root / root)
  rw [action.act_mul_group, action.act_div]
  simp only [div_eq_mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem ratioCyclotome_mul_group
    (realization : UnitKummerRootRealization action subgroup value)
    (first second : subgroup) :
    realization.ratioCyclotome (first * second) =
      realization.ratioCyclotome first *
        (KummerCyclotome.continuousAction action).act
          (first : G) (realization.ratioCyclotome second) := by
  apply MonoidHom.ext
  intro circle
  let additiveCircle : AddCircle (1 : ℚ) := circle.toAdd
  change
    realization.ratioCyclotome (first * second)
        (Multiplicative.ofAdd additiveCircle) =
      (realization.ratioCyclotome first *
        (KummerCyclotome.continuousAction action).act
          (first : G) (realization.ratioCyclotome second))
        (Multiplicative.ofAdd additiveCircle)
  induction additiveCircle using Quotient.inductionOn with
  | _ q => exact realization.ratioUnit_mul_group first second q

theorem ratioUnit_continuous
    (realization : UnitKummerRootRealization action subgroup value)
    (q : ℚ) : Continuous fun g => realization.ratioUnit g q := by
  have orbitContinuous :
      Continuous fun g : subgroup =>
        action.act (g : G) (realization.rootSystem.roots q).toMul :=
    action.continuous_action.comp
      (continuous_subtype_val.prodMk continuous_const)
  have productContinuous :=
    orbitContinuous.mul
      (continuous_const : Continuous fun _ : subgroup =>
        (realization.rootSystem.roots q).toMul⁻¹)
  convert productContinuous using 1
  funext g
  simp [ratioUnit, div_eq_mul_inv]

theorem ratioCyclotome_continuous
    (realization : UnitKummerRootRealization action subgroup value) :
    Continuous realization.ratioCyclotome := by
  rw [KummerCyclotome.continuous_iff_eval_discrete]
  intro circle
  let additiveCircle : AddCircle (1 : ℚ) := circle.toAdd
  change
    Continuous fun g => realization.ratioCyclotome g
      (Multiplicative.ofAdd additiveCircle)
  induction additiveCircle using Quotient.inductionOn with
  | _ q =>
      change Continuous fun g => realization.ratioUnit g q
      exact realization.ratioUnit_continuous q

def cocycle
    (realization : UnitKummerRootRealization action subgroup value) :
    Iut.ContinuousOneCocycle
      ((KummerCyclotome.continuousAction action).comap
        (Iut.openSubgroupInclusion subgroup)) where
  toFun := realization.ratioCyclotome
  continuous_toFun := realization.ratioCyclotome_continuous
  map_mul' := realization.ratioCyclotome_mul_group

def representative
    (realization : UnitKummerRootRealization action subgroup value) :
    Iut.ContinuousH1GermRepresentative
      (KummerCyclotome.continuousAction action) where
  subgroup := subgroup
  cocycle := realization.cocycle

noncomputable def germ
    (realization : UnitKummerRootRealization action subgroup value) :
    Iut.ContinuousH1Germ (KummerCyclotome.continuousAction action) :=
  Iut.ContinuousH1Germ.classOf realization.representative

noncomputable def localClass
    (realization : UnitKummerRootRealization action subgroup value) :
    Iut.ContinuousH1
      ((KummerCyclotome.continuousAction action).comap
        (Iut.openSubgroupInclusion subgroup)) :=
  Iut.ContinuousH1.classOf realization.cocycle

@[simp] theorem toGerm_localClass
    (realization : UnitKummerRootRealization action subgroup value) :
    Iut.ContinuousH1.toGerm subgroup realization.localClass =
      realization.germ :=
  rfl

def rootDifferenceAddHom
    (first second : CompatibleRootSystem B value) : ℚ →+ Additive B where
  toFun q := Additive.ofMul
    ((second.roots q).toMul / (first.roots q).toMul)
  map_zero' := by simp
  map_add' q r := by
    apply Additive.toMul.injective
    have firstAdd := congrArg Additive.toMul (first.roots.map_add q r)
    have secondAdd := congrArg Additive.toMul (second.roots.map_add q r)
    change (first.roots (q + r)).toMul =
      (first.roots q).toMul * (first.roots r).toMul at firstAdd
    change (second.roots (q + r)).toMul =
      (second.roots q).toMul * (second.roots r).toMul at secondAdd
    change
      (second.roots (q + r)).toMul / (first.roots (q + r)).toMul =
        ((second.roots q).toMul / (first.roots q).toMul) *
          ((second.roots r).toMul / (first.roots r).toMul)
    simp only [firstAdd, secondAdd, div_eq_mul_inv, mul_inv_rev]
    ac_rfl

omit [TopologicalSpace B] [DiscreteTopology B] in
theorem rootDifference_one
    (first second : CompatibleRootSystem B value) :
    rootDifferenceAddHom first second 1 = 0 := by
  apply Additive.toMul.injective
  change (second.roots 1).toMul / (first.roots 1).toMul = 1
  rw [congrArg Additive.toMul first.root_one,
    congrArg Additive.toMul second.root_one]
  exact div_self' value

omit [TopologicalSpace B] [DiscreteTopology B] in
theorem zmultiples_le_rootDifference_ker
    (first second : CompatibleRootSystem B value) :
    AddSubgroup.zmultiples (1 : ℚ) ≤
      (rootDifferenceAddHom first second).ker := by
  rw [AddSubgroup.zmultiples_le]
  exact rootDifference_one first second

def rootDifference
    (first second : CompatibleRootSystem B value) : KummerCyclotome B :=
  AddMonoidHom.toMultiplicativeLeft
    (QuotientAddGroup.lift
      (AddSubgroup.zmultiples (1 : ℚ))
      (rootDifferenceAddHom first second)
      (zmultiples_le_rootDifference_ker first second))

omit [TopologicalSpace B] [DiscreteTopology B] in
@[simp] theorem rootDifference_mk
    (first second : CompatibleRootSystem B value) (q : ℚ) :
    rootDifference first second
      (Multiplicative.ofAdd (q : AddCircle (1 : ℚ))) =
        (second.roots q).toMul / (first.roots q).toMul :=
  rfl

theorem representatives_equivalent
    (first second : UnitKummerRootRealization action subgroup value) :
    first.representative.Equivalent second.representative := by
  refine ⟨subgroup, le_rfl, le_rfl,
    rootDifference first.rootSystem second.rootSystem, ?_⟩
  intro g
  apply MonoidHom.ext
  intro circle
  let additiveCircle : AddCircle (1 : ℚ) := circle.toAdd
  change
    second.ratioCyclotome g (Multiplicative.ofAdd additiveCircle) =
      (rootDifference first.rootSystem second.rootSystem)⁻¹
          (Multiplicative.ofAdd additiveCircle) *
        first.ratioCyclotome g (Multiplicative.ofAdd additiveCircle) *
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

theorem germ_eq
    (first second : UnitKummerRootRealization action subgroup value) :
    first.germ = second.germ := by
  apply Quotient.sound
  exact representatives_equivalent first second

end UnitKummerRootRealization

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def continuousKummerGerm : Obligation :=
  { id := "IUT-II.continuous-unit-kummer-germ"
    source := "IUT II, Example 1.8(ii)--(iv); Absolute Anabelian Topics III, Proposition 3.2(ii)"
    status := VerificationStatus.provedKernel
    note :=
      "For a genuine discrete continuous group action, an open-subgroup-fixed " ++
        "unit and compatible rational roots construct Q/Z-valued root ratios, " ++
        "a continuous crossed homomorphism, its local H1 class, and its H1 germ. " ++
        "Changing the compatible root system is proved to change the cocycle by " ++
        "an explicit coboundary. Frobenioid evaluation and the final group/Frobenioid " ++
        "Kummer comparison remain separate obligations."
    dependsOn :=
      ["IUT-II.compatible-rational-roots-from-divisibility",
        "IUT-II.times-mu-ism-orbit"] }

end LeanFormal.IUT.Audit
