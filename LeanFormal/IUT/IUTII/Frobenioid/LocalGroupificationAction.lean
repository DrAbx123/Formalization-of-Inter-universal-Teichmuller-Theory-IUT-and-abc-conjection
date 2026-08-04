import LeanFormal.IUT.IUTII.Frobenioid.LocalMLFTMPair

/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

/-!
  The local Galois action on the groupification of the integral monoid.

  The construction is adapted from `promachina/iut-lean`,
  `Iut/Foundations/SourceThetaEvaluation.lean`, at audited commit
  `2eb61e1b037635a5346f7265f520b458155303ed` (Apache-2.0).  It is specialized
  to the literal local monoid and `TM` pair already constructed in this
  project.

  The action is extended by the Grothendieck-group universal property.  An
  equivariant identification with algebraic-closure units pulls the genuine
  Krull-open field stabilizer back to every groupification element, hence the
  action is continuous for the discrete algebraic topology.  No Frobenioid
  evaluation or Kummer injectivity is asserted here.
-/

namespace LeanFormal.IUT

namespace LocalMLFModelTMPair

variable (p : Nat) [Fact (Nat.Prime p)]

abbrev LocalGroupification :=
  Algebra.GrothendieckGroup (LocalIntegralMonoid p)

noncomputable instance localGroupificationTopology :
    TopologicalSpace (LocalGroupification p) := ⊥

noncomputable instance localGroupificationDiscreteTopology :
    DiscreteTopology (LocalGroupification p) :=
  discreteTopology_bot _

/-- Extend the arithmetic-monoid action to its Grothendieck group. -/
noncomputable def groupificationActionHom
    (pair : LocalMLFModelTMPair p) (g : pair.actingGroup) :
    LocalGroupification p →* LocalGroupification p :=
  Algebra.GrothendieckGroup.lift
    (Algebra.GrothendieckGroup.of.comp
      (pair.action p g).toMonoidHom)

@[simp]
theorem groupificationActionHom_of
    (pair : LocalMLFModelTMPair p) (g : pair.actingGroup)
    (value : LocalIntegralMonoid p) :
    pair.groupificationActionHom p g
        (Algebra.GrothendieckGroup.of value) =
      Algebra.GrothendieckGroup.of (pair.action p g value) := by
  let generatorMap :=
    Algebra.GrothendieckGroup.of.comp
      (pair.action p g).toMonoidHom
  have universalProperty :=
    Equiv.symm_apply_apply
      (Algebra.GrothendieckGroup.lift
        (M := LocalIntegralMonoid p)
        (G := LocalGroupification p))
      generatorMap
  change
    (Algebra.GrothendieckGroup.lift generatorMap).comp
        Algebra.GrothendieckGroup.of = generatorMap at universalProperty
  exact DFunLike.congr_fun universalProperty value

/-- Each extended action map is an automorphism. -/
noncomputable def groupificationActionMulAut
    (pair : LocalMLFModelTMPair p) (g : pair.actingGroup) :
    MulAut (LocalGroupification p) where
  toFun := pair.groupificationActionHom p g
  invFun := pair.groupificationActionHom p g⁻¹
  left_inv value := by
    suffices
        (pair.groupificationActionHom p g⁻¹).comp
            (pair.groupificationActionHom p g) = MonoidHom.id _ by
      exact DFunLike.congr_fun this value
    apply Algebra.GrothendieckGroup.lift.symm.injective
    ext monoidValue
    simp only [Algebra.GrothendieckGroup.lift_symm_apply,
      MonoidHom.comp_apply, groupificationActionHom_of,
      MonoidHom.id_apply]
    rw [map_inv]
    exact congrArg Algebra.GrothendieckGroup.of
      ((pair.action p g).symm_apply_apply monoidValue)
  right_inv value := by
    suffices
        (pair.groupificationActionHom p g).comp
            (pair.groupificationActionHom p g⁻¹) = MonoidHom.id _ by
      exact DFunLike.congr_fun this value
    apply Algebra.GrothendieckGroup.lift.symm.injective
    ext monoidValue
    simp only [Algebra.GrothendieckGroup.lift_symm_apply,
      MonoidHom.comp_apply, groupificationActionHom_of,
      MonoidHom.id_apply]
    rw [map_inv]
    exact congrArg Algebra.GrothendieckGroup.of
      ((pair.action p g).apply_symm_apply monoidValue)
  map_mul' first second :=
    map_mul (pair.groupificationActionHom p g) first second

@[simp]
theorem groupificationActionMulAut_of
    (pair : LocalMLFModelTMPair p) (g : pair.actingGroup)
    (value : LocalIntegralMonoid p) :
    pair.groupificationActionMulAut p g
        (Algebra.GrothendieckGroup.of value) =
      Algebra.GrothendieckGroup.of (pair.action p g value) :=
  pair.groupificationActionHom_of p g value

theorem groupificationActionHom_one
    (pair : LocalMLFModelTMPair p) :
    pair.groupificationActionHom p 1 = MonoidHom.id _ := by
  apply Algebra.GrothendieckGroup.lift.symm.injective
  ext monoidValue
  simp only [Algebra.GrothendieckGroup.lift_symm_apply,
    MonoidHom.comp_apply, groupificationActionHom_of,
    MonoidHom.id_apply, map_one]
  rfl

theorem groupificationActionHom_mul
    (pair : LocalMLFModelTMPair p) (first second : pair.actingGroup) :
    pair.groupificationActionHom p (first * second) =
      (pair.groupificationActionHom p first).comp
        (pair.groupificationActionHom p second) := by
  apply Algebra.GrothendieckGroup.lift.symm.injective
  ext monoidValue
  simp only [Algebra.GrothendieckGroup.lift_symm_apply,
    MonoidHom.comp_apply, groupificationActionHom_of, map_mul]
  rfl

/-- The extended automorphisms form a genuine action. -/
noncomputable def groupificationAction
    (pair : LocalMLFModelTMPair p) :
    pair.actingGroup →* MulAut (LocalGroupification p) where
  toFun := pair.groupificationActionMulAut p
  map_one' := by
    apply MulEquiv.ext
    intro value
    exact DFunLike.congr_fun (pair.groupificationActionHom_one p) value
  map_mul' first second := by
    apply MulEquiv.ext
    intro value
    exact DFunLike.congr_fun
      (pair.groupificationActionHom_mul p first second) value

@[implicit_reducible]
noncomputable def groupificationMulAction
    (pair : LocalMLFModelTMPair p) :
    MulAction pair.actingGroup (LocalGroupification p) :=
  MulAction.compHom _ (pair.groupificationAction p)

/-- The groupification action is the transported algebraic-closure action. -/
theorem groupificationEquivAlgebraicClosureUnits_action
    (pair : LocalMLFModelTMPair p) (g : pair.actingGroup)
    (value : LocalGroupification p) :
    LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p
        (pair.groupificationAction p g value) =
      localGaloisUnitsAction p (pair.augmentation g)
        (LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p value) := by
  suffices
      (LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p).toMonoidHom.comp
          (pair.groupificationActionHom p g) =
        (localGaloisUnitsAction p (pair.augmentation g)).toMonoidHom.comp
          (LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p).toMonoidHom by
    exact DFunLike.congr_fun this value
  apply Algebra.GrothendieckGroup.lift.symm.injective
  ext monoidValue
  simp only [Algebra.GrothendieckGroup.lift_symm_apply,
    MonoidHom.comp_apply, groupificationActionHom_of]
  unfold LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits
  change
    ((↑(LocalIntegralMonoid.groupificationToAlgebraicClosureUnits p
        (Algebra.GrothendieckGroup.of (pair.action p g monoidValue))) :
          AlgebraicClosure ℚ_[p])) =
      ((↑(localGaloisUnitsAction p (pair.augmentation g)
        (LocalIntegralMonoid.groupificationToAlgebraicClosureUnits p
          (Algebra.GrothendieckGroup.of monoidValue))) :
            AlgebraicClosure ℚ_[p]))
  rw [LocalIntegralMonoid.groupificationToAlgebraicClosureUnits_of,
    LocalIntegralMonoid.groupificationToAlgebraicClosureUnits_of]
  rfl

/-- The Krull-open stabilizer of the corresponding algebraic-closure unit. -/
noncomputable def algebraicClosureUnitOpenStabilizer
    (value : (AlgebraicClosure ℚ_[p])ˣ) :
    OpenSubgroup (LocalAbsoluteGalois p) :=
  ⟨MulAction.stabilizer (LocalAbsoluteGalois p)
      (value : AlgebraicClosure ℚ_[p]),
    stabilizer_isOpen_of_isIntegral
      (K := ℚ_[p]) (L := AlgebraicClosure ℚ_[p])
      (value : AlgebraicClosure ℚ_[p])⟩

/-- Pull the actual Krull stabilizer back along the `TM` augmentation. -/
noncomputable def groupificationOpenStabilizer
    (pair : LocalMLFModelTMPair p) (value : LocalGroupification p) :
    OpenSubgroup pair.actingGroup :=
  (algebraicClosureUnitOpenStabilizer p
      (LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p value)).comap
    pair.augmentation.toMonoidHom pair.augmentation.continuous_toFun

theorem groupificationOpenStabilizer_fixed
    (pair : LocalMLFModelTMPair p) (value : LocalGroupification p)
    (g : pair.groupificationOpenStabilizer p value) :
    pair.groupificationAction p (g : pair.actingGroup) value = value := by
  apply (LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p).injective
  rw [pair.groupificationEquivAlgebraicClosureUnits_action p]
  apply Units.ext
  exact g.property

theorem groupification_stabilizer_isOpen
    (pair : LocalMLFModelTMPair p) (value : LocalGroupification p) :
    letI := pair.groupificationMulAction p
    IsOpen (MulAction.stabilizer pair.actingGroup value : Set pair.actingGroup) := by
  letI := pair.groupificationMulAction p
  apply Subgroup.isOpen_mono
    (H₁ := pair.groupificationOpenStabilizer p value)
    (H₂ := MulAction.stabilizer pair.actingGroup value)
  · intro g hg
    exact pair.groupificationOpenStabilizer_fixed p value ⟨g, hg⟩
  · exact (pair.groupificationOpenStabilizer p value).isOpen

set_option synthInstance.maxHeartbeats 100000 in
-- The induced `SMul` instance unfolds the Grothendieck universal-property action.
theorem groupificationAction_continuous_discrete
    (pair : LocalMLFModelTMPair p) :
    letI := pair.groupificationMulAction p
    ContinuousSMul pair.actingGroup (LocalGroupification p) := by
  letI := pair.groupificationMulAction p
  exact continuousSMul_iff_stabilizer_isOpen.mpr
    (pair.groupification_stabilizer_isOpen p)

set_option maxHeartbeats 800000 in
-- Joint-continuity elaboration unfolds the action and the open-stabilizer proof.
set_option synthInstance.maxHeartbeats 100000 in
-- The corresponding `SMul` instance is obtained through the Grothendieck action.
/-- The actual discrete continuous groupification action. -/
noncomputable def discreteGroupificationAction
    (pair : LocalMLFModelTMPair p) :
    DiscreteContinuousGroupAction pair.actingGroup (LocalGroupification p) where
  automorphism := pair.groupificationAction p
  continuous_action := by
    letI := pair.groupificationMulAction p
    letI : ContinuousSMul pair.actingGroup (LocalGroupification p) :=
      pair.groupificationAction_continuous_discrete p
    exact continuous_smul

/-- Embed units of the integral monoid in its groupification. -/
noncomputable def unitGrothendieckHom :
    (LocalIntegralMonoid p)ˣ →* LocalGroupification p :=
  Algebra.GrothendieckGroup.of.comp
    { toFun := Units.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem unitGrothendieckHom_injective :
    Function.Injective (unitGrothendieckHom p) := by
  intro first second equality
  apply LocalIntegralMonoid.unitEvaluation_injective p
  apply Units.ext
  have transported := congrArg
    (LocalIntegralMonoid.groupificationEquivAlgebraicClosureUnits p) equality
  change
    LocalIntegralMonoid.groupificationToAlgebraicClosureUnits p
        (Algebra.GrothendieckGroup.of (first : LocalIntegralMonoid p)) =
      LocalIntegralMonoid.groupificationToAlgebraicClosureUnits p
        (Algebra.GrothendieckGroup.of (second : LocalIntegralMonoid p))
    at transported
  rw [LocalIntegralMonoid.groupificationToAlgebraicClosureUnits_of,
    LocalIntegralMonoid.groupificationToAlgebraicClosureUnits_of] at transported
  exact congrArg Units.val transported

@[simp]
theorem unitGrothendieckHom_action
    (pair : LocalMLFModelTMPair p) (g : pair.actingGroup)
    (unit : (LocalIntegralMonoid p)ˣ) :
    pair.groupificationAction p g (unitGrothendieckHom p unit) =
      unitGrothendieckHom p
        (Units.map (pair.action p g).toMonoidHom unit) := by
  exact pair.groupificationActionMulAut_of p g unit

end LocalMLFModelTMPair

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localGroupificationAction : Obligation :=
  { id := "IUT-II.local-groupification-Galois-action"
    source := "Absolute Anabelian Topics III, Proposition 3.2(ii); local MLF groupification action"
    status := VerificationStatus.proved
    note :=
      "The actual local integral-monoid Galois action is extended through the " ++
        "Grothendieck-group universal property. Its stabilizer is pulled back " ++
        "from the genuine Krull-open algebraic-closure stabilizer, yielding a " ++
        "genuine discrete continuous action. The unit embedding is injective and " ++
        "equivariant, and the groupification equivalence is proved equivariant " ++
        "with the actual action on algebraic-closure units. No Frobenioid " ++
        "evaluation or Kummer injectivity is asserted."
    dependsOn :=
      [ "IUT-II.local-MLF-TM-pair",
        "IUT-II.local-torsion-cyclotome" ] }

end LeanFormal.IUT.Audit
