import LeanFormal.IUT.IUTII.Frobenioid.LocalGroupificationAction

/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

/-!
  Integral-unit-valued local Kummer root ratios.

  The root-ratio argument is adapted from `promachina/iut-lean`,
  `Iut/Foundations/SourceThetaEvaluation.lean`, at audited commit
  `2eb61e1b037635a5346f7265f520b458155303ed` (Apache-2.0).  The code here is
  specialized to this project's actual local integral monoid and removes the
  source repository's reconstruction wrappers.

  Compatible rational roots live in the Grothendieck group of the nonzero
  integral monoid.  Two root systems for the same value differ at exponent
  `q` by an element killed by `q.den`.  The proved local torsion theorem then
  lifts this quotient uniquely to a unit of the integral monoid.  Applied to a
  root system and its Galois translate, this produces the integral-unit-valued
  cyclotome and continuous crossed cocycle required by the local Kummer input.
-/

namespace LeanFormal.IUT

namespace LocalMLFModelTMPair

variable (p : Nat) [Fact (Nat.Prime p)]

noncomputable instance localIntegralUnitTopology :
    TopologicalSpace (LocalIntegralMonoid p)ˣ := ⊥

noncomputable instance localIntegralUnitDiscreteTopology :
    DiscreteTopology (LocalIntegralMonoid p)ˣ :=
  discreteTopology_bot _

@[simp]
theorem groupificationEquiv_unitGrothendieckHom
    (unit : (LocalIntegralMonoid p)ˣ) :
    LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p
        (unitGrothendieckHom p unit) =
      LocalIntegralMonoid.unitEvaluation p unit := by
  change
    LocalIntegralMonoid.groupificationToAlgebraicClosureUnits p
        (Algebra.GrothendieckGroup.of
          (unit : LocalIntegralMonoid p)) =
      LocalIntegralMonoid.unitEvaluation p unit
  rw [LocalIntegralMonoid.groupificationToAlgebraicClosureUnits_of]
  rfl

/-- Restriction of the unit embedding to the full torsion subgroups. -/
noncomputable def torsionUnitToGroupificationTorsion :
    CommGroup.torsion (LocalIntegralMonoid p)ˣ →*
      CommGroup.torsion (LocalGroupification p) where
  toFun unit :=
    ⟨unitGrothendieckHom p (unit : (LocalIntegralMonoid p)ˣ),
      (CommGroup.mem_torsion _).mpr
        ((unitGrothendieckHom p).isOfFinOrder
          ((CommGroup.mem_torsion (unit : (LocalIntegralMonoid p)ˣ)).mp
            unit.property))⟩
  map_one' := Subtype.ext (map_one (unitGrothendieckHom p))
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul (unitGrothendieckHom p)
      (first : (LocalIntegralMonoid p)ˣ)
      (second : (LocalIntegralMonoid p)ˣ)

theorem torsionUnitToGroupificationTorsion_bijective :
    Function.Bijective (torsionUnitToGroupificationTorsion p) := by
  constructor
  · intro first second equality
    apply Subtype.ext
    apply unitGrothendieckHom_injective p
    exact congrArg Subtype.val equality
  · intro target
    rcases isOfFinOrder_iff_pow_eq_one.mp
        ((CommGroup.mem_torsion
          (target : LocalGroupification p)).mp target.property) with
      ⟨n, hn, target_pow⟩
    let fieldValue :=
      LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p
        (target : LocalGroupification p)
    have field_pow : fieldValue ^ n = 1 := by
      calc
        fieldValue ^ n =
            LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p
              ((target : LocalGroupification p) ^ n) :=
          (map_pow
            (LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p)
            (target : LocalGroupification p) n).symm
        _ = LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p 1 :=
          congrArg
            (LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p)
            target_pow
        _ = 1 := map_one _
    let sourceUnit :=
      LocalIntegralMonoid.torsionUnit p fieldValue n hn.ne' field_pow
    have source_eq :
        unitGrothendieckHom p sourceUnit =
          (target : LocalGroupification p) := by
      apply
        (LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p).injective
      rw [groupificationEquiv_unitGrothendieckHom]
      exact LocalIntegralMonoid.unitEvaluation_torsionUnit
        p fieldValue n hn.ne' field_pow
    have source_pow : sourceUnit ^ n = 1 := by
      apply unitGrothendieckHom_injective p
      rw [map_pow, map_one, source_eq, target_pow]
    let sourceTorsion : CommGroup.torsion (LocalIntegralMonoid p)ˣ :=
      ⟨sourceUnit,
        (CommGroup.mem_torsion sourceUnit).mpr
          (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, source_pow⟩)⟩
    refine ⟨sourceTorsion, ?_⟩
    apply Subtype.ext
    exact source_eq

/-- Torsion in the local groupification is exactly the torsion of the actual
integral-unit group. -/
noncomputable def torsionUnitEquivGroupificationTorsion :
    CommGroup.torsion (LocalIntegralMonoid p)ˣ ≃*
      CommGroup.torsion (LocalGroupification p) :=
  MulEquiv.ofBijective
    (torsionUnitToGroupificationTorsion p)
    (torsionUnitToGroupificationTorsion_bijective p)

@[implicit_reducible]
noncomputable def integralUnitMulAction
    (pair : LocalMLFModelTMPair p) :
    MulAction pair.actingGroup (LocalIntegralMonoid p)ˣ :=
  MulAction.compHom _ (pair.unitAction p)

theorem integralUnitAction_continuous_discrete
    (pair : LocalMLFModelTMPair p) :
    letI := pair.integralUnitMulAction p
    ContinuousSMul pair.actingGroup (LocalIntegralMonoid p)ˣ := by
  letI := pair.integralUnitMulAction p
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro unit
  apply Subgroup.isOpen_mono
    (H₁ := pair.groupificationOpenStabilizer p
      (unitGrothendieckHom p unit))
    (H₂ := MulAction.stabilizer pair.actingGroup unit)
  · intro g hg
    change pair.unitAction p g unit = unit
    apply unitGrothendieckHom_injective p
    change
      unitGrothendieckHom p
          (Units.map (pair.action p g).toMonoidHom unit) =
        unitGrothendieckHom p unit
    rw [← pair.unitGrothendieckHom_action p]
    exact pair.groupificationOpenStabilizer_fixed p
      (unitGrothendieckHom p unit) ⟨g, hg⟩
  · exact (pair.groupificationOpenStabilizer p
      (unitGrothendieckHom p unit)).isOpen

/-- The actual continuous action on the discrete integral-unit group. -/
noncomputable def discreteIntegralUnitAction
    (pair : LocalMLFModelTMPair p) :
    DiscreteContinuousGroupAction pair.actingGroup
      (LocalIntegralMonoid p)ˣ where
  automorphism := pair.unitAction p
  continuous_action := by
    letI := pair.integralUnitMulAction p
    letI : ContinuousSMul pair.actingGroup (LocalIntegralMonoid p)ˣ :=
      pair.integralUnitAction_continuous_discrete p
    exact continuous_smul

/-- Every quotient of compatible roots for one local monoid value is represented
by a unique integral unit. -/
theorem quotientUnit_exists
    (value : LocalIntegralMonoid p)
    (first second : CompatibleRootSystem
      (LocalGroupification p) (Algebra.GrothendieckGroup.of value))
    (q : ℚ) :
    ∃ unit : (LocalIntegralMonoid p)ˣ,
      unitGrothendieckHom p unit =
        (second.roots q).toMul / (first.roots q).toMul := by
  let quotient := (second.roots q).toMul / (first.roots q).toMul
  have quotient_pow : quotient ^ q.den = 1 :=
    CompatibleRootSystem.quotient_pow_den first second q
  have quotient_torsion : IsOfFinOrder quotient :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨q.den, Nat.pos_of_ne_zero q.den_ne_zero, quotient_pow⟩
  let target : CommGroup.torsion (LocalGroupification p) :=
    ⟨quotient, (CommGroup.mem_torsion quotient).mpr quotient_torsion⟩
  let source := (torsionUnitEquivGroupificationTorsion p).symm target
  refine ⟨(source : (LocalIntegralMonoid p)ˣ), ?_⟩
  have lifted :=
    (torsionUnitEquivGroupificationTorsion p).apply_symm_apply target
  exact congrArg Subtype.val lifted

/-- Galois translation of a compatible root system when the base monoid value
is fixed. -/
noncomputable def galoisTranslateRootSystem
    (pair : LocalMLFModelTMPair p)
    (value : LocalIntegralMonoid p)
    (rootSystem : CompatibleRootSystem
      (LocalGroupification p) (Algebra.GrothendieckGroup.of value))
    (g : pair.actingGroup)
    (fixed : pair.action p g value = value) :
    CompatibleRootSystem
      (LocalGroupification p) (Algebra.GrothendieckGroup.of value) where
  roots :=
    { toFun := fun q => Additive.ofMul
        (pair.groupificationAction p g (rootSystem.roots q).toMul)
      map_zero' := by
        apply Additive.toMul.injective
        change
          pair.groupificationAction p g (rootSystem.roots 0).toMul = 1
        have root_zero := congrArg Additive.toMul rootSystem.roots.map_zero
        change (rootSystem.roots 0).toMul = 1 at root_zero
        rw [root_zero, map_one]
      map_add' first second := by
        apply Additive.toMul.injective
        change
          pair.groupificationAction p g
              (rootSystem.roots (first + second)).toMul =
            pair.groupificationAction p g (rootSystem.roots first).toMul *
              pair.groupificationAction p g (rootSystem.roots second).toMul
        have root_add := congrArg Additive.toMul
          (rootSystem.roots.map_add first second)
        change
          (rootSystem.roots (first + second)).toMul =
            (rootSystem.roots first).toMul *
              (rootSystem.roots second).toMul at root_add
        rw [root_add, map_mul] }
  root_one := by
    change
      Additive.ofMul
          (pair.groupificationAction p g (rootSystem.roots 1).toMul) =
        Additive.ofMul (Algebra.GrothendieckGroup.of value)
    apply Additive.toMul.injective
    change
      pair.groupificationAction p g (rootSystem.roots 1).toMul =
        Algebra.GrothendieckGroup.of value
    have root_one := congrArg Additive.toMul rootSystem.root_one
    change
      (rootSystem.roots 1).toMul =
        Algebra.GrothendieckGroup.of value at root_one
    rw [root_one]
    have action_of := pair.groupificationActionMulAut_of p g value
    change
      pair.groupificationAction p g
          (Algebra.GrothendieckGroup.of value) =
        Algebra.GrothendieckGroup.of (pair.action p g value) at action_of
    rw [action_of, fixed]

/-- Compatible roots of a local monoid element together with their actual
integral-unit Galois ratios. -/
structure IntegralKummerRootRealization
    (pair : LocalMLFModelTMPair p)
    (subgroup : OpenSubgroup pair.actingGroup)
    (value : LocalIntegralMonoid p) where
  fixed : ∀ g : subgroup, pair.action p (g : pair.actingGroup) value = value
  rootSystem : CompatibleRootSystem
    (LocalGroupification p) (Algebra.GrothendieckGroup.of value)
  ratioUnit : subgroup → ℚ → (LocalIntegralMonoid p)ˣ
  ratio_spec : ∀ (g : subgroup) (q : ℚ),
    unitGrothendieckHom p (ratioUnit g q) =
      pair.groupificationAction p (g : pair.actingGroup)
          (rootSystem.roots q).toMul /
        (rootSystem.roots q).toMul

namespace IntegralKummerRootRealization

variable
  {p : Nat} [Fact (Nat.Prime p)]
  {pair : LocalMLFModelTMPair p}
  {subgroup : OpenSubgroup pair.actingGroup}
  {value : LocalIntegralMonoid p}

noncomputable def ofRootSystem
    (pair : LocalMLFModelTMPair p)
    (subgroup : OpenSubgroup pair.actingGroup)
    (value : LocalIntegralMonoid p)
    (fixed : ∀ g : subgroup,
      pair.action p (g : pair.actingGroup) value = value)
    (rootSystem : CompatibleRootSystem
      (LocalGroupification p) (Algebra.GrothendieckGroup.of value)) :
    IntegralKummerRootRealization p pair subgroup value where
  fixed := fixed
  rootSystem := rootSystem
  ratioUnit g q := Classical.choose
    (quotientUnit_exists p value rootSystem
      (galoisTranslateRootSystem p pair value rootSystem
        (g : pair.actingGroup) (fixed g)) q)
  ratio_spec g q := Classical.choose_spec
    (quotientUnit_exists p value rootSystem
      (galoisTranslateRootSystem p pair value rootSystem
        (g : pair.actingGroup) (fixed g)) q)

theorem ratioUnit_zero
    (realization : IntegralKummerRootRealization p pair subgroup value)
    (g : subgroup) : realization.ratioUnit g 0 = 1 := by
  apply unitGrothendieckHom_injective p
  rw [realization.ratio_spec]
  simp

theorem ratioUnit_add
    (realization : IntegralKummerRootRealization p pair subgroup value)
    (g : subgroup) (first second : ℚ) :
    realization.ratioUnit g (first + second) =
      realization.ratioUnit g first * realization.ratioUnit g second := by
  apply unitGrothendieckHom_injective p
  rw [map_mul, realization.ratio_spec, realization.ratio_spec,
    realization.ratio_spec]
  have roots_add := congrArg Additive.toMul
    (realization.rootSystem.roots.map_add first second)
  change
    (realization.rootSystem.roots (first + second)).toMul =
      (realization.rootSystem.roots first).toMul *
        (realization.rootSystem.roots second).toMul at roots_add
  rw [roots_add, map_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

noncomputable def ratioAddHom
    (realization : IntegralKummerRootRealization p pair subgroup value)
    (g : subgroup) : ℚ →+ Additive (LocalIntegralMonoid p)ˣ where
  toFun q := Additive.ofMul (realization.ratioUnit g q)
  map_zero' := congrArg Additive.ofMul (realization.ratioUnit_zero g)
  map_add' first second := congrArg Additive.ofMul
    (realization.ratioUnit_add g first second)

theorem ratioUnit_one
    (realization : IntegralKummerRootRealization p pair subgroup value)
    (g : subgroup) : realization.ratioUnit g 1 = 1 := by
  apply unitGrothendieckHom_injective p
  rw [realization.ratio_spec]
  have root_one := congrArg Additive.toMul realization.rootSystem.root_one
  change
    (realization.rootSystem.roots 1).toMul =
      Algebra.GrothendieckGroup.of value at root_one
  rw [root_one]
  have action_of := pair.groupificationActionMulAut_of p
    (g : pair.actingGroup) value
  change
    pair.groupificationAction p (g : pair.actingGroup)
        (Algebra.GrothendieckGroup.of value) =
      Algebra.GrothendieckGroup.of
        (pair.action p (g : pair.actingGroup) value) at action_of
  rw [action_of, realization.fixed, map_one]
  simp

theorem zmultiples_le_ratioAddHom_ker
    (realization : IntegralKummerRootRealization p pair subgroup value)
    (g : subgroup) :
    AddSubgroup.zmultiples (1 : ℚ) ≤ (realization.ratioAddHom g).ker := by
  rw [AddSubgroup.zmultiples_le]
  change realization.ratioAddHom g 1 = 0
  apply Additive.toMul.injective
  exact realization.ratioUnit_one g

/-- The integral-unit-valued local cyclotome `mu_Z(M)`. -/
noncomputable def ratioCyclotome
    (realization : IntegralKummerRootRealization p pair subgroup value)
    (g : subgroup) : KummerCyclotome (LocalIntegralMonoid p)ˣ :=
  AddMonoidHom.toMultiplicativeLeft
    (QuotientAddGroup.lift
      (AddSubgroup.zmultiples (1 : ℚ))
      (realization.ratioAddHom g)
      (realization.zmultiples_le_ratioAddHom_ker g))

@[simp]
theorem ratioCyclotome_mk
    (realization : IntegralKummerRootRealization p pair subgroup value)
    (g : subgroup) (q : ℚ) :
    realization.ratioCyclotome g
        (Multiplicative.ofAdd (q : AddCircle (1 : ℚ))) =
      realization.ratioUnit g q :=
  rfl

theorem ratioUnit_mul_group
    (realization : IntegralKummerRootRealization p pair subgroup value)
    (first second : subgroup) (q : ℚ) :
    realization.ratioUnit (first * second) q =
      realization.ratioUnit first q *
        Units.map (pair.action p (first : pair.actingGroup)).toMonoidHom
          (realization.ratioUnit second q) := by
  apply unitGrothendieckHom_injective p
  rw [map_mul, ← pair.unitGrothendieckHom_action p]
  rw [realization.ratio_spec, realization.ratio_spec,
    realization.ratio_spec]
  change
    pair.groupificationAction p
          ((first : pair.actingGroup) * (second : pair.actingGroup))
          (realization.rootSystem.roots q).toMul /
        (realization.rootSystem.roots q).toMul =
      (pair.groupificationAction p (first : pair.actingGroup)
            (realization.rootSystem.roots q).toMul /
          (realization.rootSystem.roots q).toMul) *
        pair.groupificationAction p (first : pair.actingGroup)
          (pair.groupificationAction p (second : pair.actingGroup)
              (realization.rootSystem.roots q).toMul /
            (realization.rootSystem.roots q).toMul)
  have action_mul :
      pair.groupificationAction p
          ((first : pair.actingGroup) * (second : pair.actingGroup))
          (realization.rootSystem.roots q).toMul =
        pair.groupificationAction p (first : pair.actingGroup)
          (pair.groupificationAction p (second : pair.actingGroup)
            (realization.rootSystem.roots q).toMul) :=
    DFunLike.congr_fun
      (pair.groupificationActionHom_mul p
        (first : pair.actingGroup) (second : pair.actingGroup))
      (realization.rootSystem.roots q).toMul
  rw [action_mul, map_div, mul_comm, div_mul_div_cancel]

theorem ratioCyclotome_mul_group
    (realization : IntegralKummerRootRealization p pair subgroup value)
    (first second : subgroup) :
    realization.ratioCyclotome (first * second) =
      realization.ratioCyclotome first *
        (KummerCyclotome.continuousAction
          (pair.discreteIntegralUnitAction p)).act
          (first : pair.actingGroup) (realization.ratioCyclotome second) := by
  apply MonoidHom.ext
  intro circle
  let additiveCircle : AddCircle (1 : ℚ) := circle.toAdd
  change
    realization.ratioCyclotome (first * second)
        (Multiplicative.ofAdd additiveCircle) =
      (realization.ratioCyclotome first *
        (KummerCyclotome.continuousAction
          (pair.discreteIntegralUnitAction p)).act
          (first : pair.actingGroup) (realization.ratioCyclotome second))
        (Multiplicative.ofAdd additiveCircle)
  induction additiveCircle using Quotient.inductionOn with
  | _ q => exact realization.ratioUnit_mul_group first second q

theorem ratioUnit_isLocallyConstant
    (realization : IntegralKummerRootRealization p pair subgroup value)
    (q : ℚ) :
    IsLocallyConstant fun g : subgroup => realization.ratioUnit g q := by
  let groupRealization : UnitKummerRootRealization
      (pair.discreteGroupificationAction p) subgroup
      (Algebra.GrothendieckGroup.of value) :=
    { fixed := fun g => by
        change
          pair.groupificationAction p (g : pair.actingGroup)
              (Algebra.GrothendieckGroup.of value) =
            Algebra.GrothendieckGroup.of value
        have action_of := pair.groupificationActionMulAut_of p
          (g : pair.actingGroup) value
        change
          pair.groupificationAction p (g : pair.actingGroup)
              (Algebra.GrothendieckGroup.of value) =
            Algebra.GrothendieckGroup.of
              (pair.action p (g : pair.actingGroup) value) at action_of
        rw [action_of, realization.fixed]
      rootSystem := realization.rootSystem }
  have embeddedLocallyConstant : IsLocallyConstant
      (unitGrothendieckHom p ∘
        fun g : subgroup => realization.ratioUnit g q) := by
    have embedded_eq :
        (unitGrothendieckHom p ∘
            fun g : subgroup => realization.ratioUnit g q) =
          fun g : subgroup => groupRealization.ratioUnit g q := by
      funext g
      exact realization.ratio_spec g q
    rw [embedded_eq]
    exact (IsLocallyConstant.iff_continuous _).mpr
      (groupRealization.ratioUnit_continuous q)
  exact IsLocallyConstant.desc
    (fun g : subgroup => realization.ratioUnit g q)
    (unitGrothendieckHom p) embeddedLocallyConstant
    (unitGrothendieckHom_injective p)

theorem ratioCyclotome_continuous
    (realization : IntegralKummerRootRealization p pair subgroup value) :
    Continuous realization.ratioCyclotome := by
  rw [KummerCyclotome.continuous_iff_eval_discrete]
  intro circle
  let additiveCircle : AddCircle (1 : ℚ) := circle.toAdd
  change Continuous fun g => realization.ratioCyclotome g
    (Multiplicative.ofAdd additiveCircle)
  induction additiveCircle using Quotient.inductionOn with
  | _ q =>
      exact (IsLocallyConstant.iff_continuous _).mp
        (realization.ratioUnit_isLocallyConstant q)

noncomputable def cocycle
    (realization : IntegralKummerRootRealization p pair subgroup value) :
    Iut.ContinuousOneCocycle
      ((KummerCyclotome.continuousAction
        (pair.discreteIntegralUnitAction p)).comap
        (Iut.openSubgroupInclusion subgroup)) where
  toFun := realization.ratioCyclotome
  continuous_toFun := realization.ratioCyclotome_continuous
  map_mul' := realization.ratioCyclotome_mul_group

noncomputable def representative
    (realization : IntegralKummerRootRealization p pair subgroup value) :
    Iut.ContinuousH1GermRepresentative
      (KummerCyclotome.continuousAction
        (pair.discreteIntegralUnitAction p)) where
  subgroup := subgroup
  cocycle := realization.cocycle

noncomputable def germ
    (realization : IntegralKummerRootRealization p pair subgroup value) :
    Iut.ContinuousH1Germ
      (KummerCyclotome.continuousAction
        (pair.discreteIntegralUnitAction p)) :=
  Iut.ContinuousH1Germ.classOf realization.representative

end IntegralKummerRootRealization

/-- The canonical integral Kummer root realization on the actual Krull-open
stabilizer of a local monoid value. -/
noncomputable def canonicalIntegralKummerRootRealization
    (pair : LocalMLFModelTMPair p) (value : LocalIntegralMonoid p) :
    IntegralKummerRootRealization p pair (pair.openStabilizer p value) value :=
  IntegralKummerRootRealization.ofRootSystem
    pair (pair.openStabilizer p value) value
    (pair.openStabilizer_fixed p value)
    (LocalIntegralMonoid.groupificationCompatibleRoots p
      (Algebra.GrothendieckGroup.of value))

end LocalMLFModelTMPair

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localIntegralUnitKummer : Obligation :=
  { id := "IUT-II.local-integral-unit-Kummer-realization"
    source := "Absolute Anabelian Topics III, Proposition 3.2(ii); IUT II, Example 1.8(ii)-(iv)"
    status := VerificationStatus.proved
    note :=
      "Compatible rational roots are constructed in the actual Grothendieck " ++
        "group of the local integral monoid. Lean proves that every Galois " ++
        "root ratio is torsion, lifts it uniquely to an actual integral unit, " ++
        "and constructs the resulting unit-valued Q/Z cyclotome, continuous " ++
        "crossed cocycle, and H1 germ. Canonical root-choice independence and " ++
        "mono-analytic injectivity are discharged in the two following " ++
        "modules; Frobenioid-side evaluation remains a separate obligation."
    dependsOn :=
      [ "IUT-II.local-groupification-Galois-action",
        "IUT-II.continuous-unit-kummer-germ" ] }

end LeanFormal.IUT.Audit
