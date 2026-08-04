/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

namespace LeanFormal.IUT

/-!
  Compatible rational powers from genuine divisibility.

  This is adapted from the rational-root construction in
  `promachina/iut-lean`, `SourceThetaEvaluation.lean`, last changed by upstream
  commit `3de1d7c1`, under Apache-2.0.  The inclusion `ℤ → ℚ` is extended by
  injectivity of divisible abelian groups, so the output is one additive
  homomorphism `ℚ → Additive B`, not a family of unrelated root choices.
-/

universe u

@[implicit_reducible]
noncomputable def additiveDivisibleByNatOfRootable
    {B : Type u} [CommGroup B] [RootableBy B ℕ] :
    DivisibleBy (Additive B) ℕ where
  div value n := Additive.ofMul (RootableBy.root value.toMul n)
  div_zero value := by
    change RootableBy.root value.toMul 0 = 1
    exact RootableBy.root_zero value.toMul
  div_cancel value hn := by
    change RootableBy.root value.toMul _ ^ _ = value.toMul
    exact RootableBy.root_cancel value.toMul hn

noncomputable def rootableRationalPowers
    {B : Type u} [CommGroup B] [RootableBy B ℕ]
    (value : B) : ℚ →+ Additive B := by
  letI : DivisibleBy (Additive B) ℕ :=
    additiveDivisibleByNatOfRootable
  letI : DivisibleBy (Additive B) ℤ :=
    AddGroup.divisibleByIntOfDivisibleByNat (Additive B)
  let integerMap :
      AddCommGrpCat.of (ULift.{u} ℤ) ⟶ AddCommGrpCat.of (Additive B) :=
    AddCommGrpCat.ofHom
      (uliftZMultiplesHom (Additive B) (Additive.ofMul value))
  let integerInRational :
      AddCommGrpCat.of (ULift.{u} ℤ) ⟶ AddCommGrpCat.of (ULift.{u} ℚ) :=
    AddCommGrpCat.ofHom
      (AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((Int.castAddHom ℚ).comp AddEquiv.ulift.toAddMonoidHom))
  letI : CategoryTheory.Mono integerInRational :=
    CategoryTheory.ConcreteCategory.mono_of_injective
      integerInRational (by
        intro first second equality
        apply ULift.ext
        exact Int.cast_injective
          (show (first.down : ℚ) = second.down from
            congrArg ULift.down equality))
  exact
    (CategoryTheory.Injective.factorThru
      integerMap integerInRational).hom.comp
        AddEquiv.ulift.symm.toAddMonoidHom

theorem rootableRationalPowers_one
    {B : Type u} [CommGroup B] [RootableBy B ℕ]
    (value : B) :
    rootableRationalPowers value 1 = Additive.ofMul value := by
  letI : DivisibleBy (Additive B) ℕ :=
    additiveDivisibleByNatOfRootable
  letI : DivisibleBy (Additive B) ℤ :=
    AddGroup.divisibleByIntOfDivisibleByNat (Additive B)
  let integerMap :
      AddCommGrpCat.of (ULift.{u} ℤ) ⟶ AddCommGrpCat.of (Additive B) :=
    AddCommGrpCat.ofHom
      (uliftZMultiplesHom (Additive B) (Additive.ofMul value))
  let integerInRational :
      AddCommGrpCat.of (ULift.{u} ℤ) ⟶ AddCommGrpCat.of (ULift.{u} ℚ) :=
    AddCommGrpCat.ofHom
      (AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((Int.castAddHom ℚ).comp AddEquiv.ulift.toAddMonoidHom))
  letI : CategoryTheory.Mono integerInRational :=
    CategoryTheory.ConcreteCategory.mono_of_injective
      integerInRational (by
        intro first second equality
        apply ULift.ext
        exact Int.cast_injective
          (show (first.down : ℚ) = second.down from
            congrArg ULift.down equality))
  have factorization :=
    CategoryTheory.Injective.comp_factorThru integerMap integerInRational
  have atOne := CategoryTheory.congr_fun factorization (ULift.up (1 : ℤ))
  rw [AddCommGrpCat.comp_apply] at atOne
  have integerInRational_one :
      integerInRational (ULift.up (1 : ℤ)) = ULift.up (1 : ℚ) := rfl
  have integerMap_one :
      integerMap (ULift.up (1 : ℤ)) = Additive.ofMul value := by
    change (1 : ℤ) • Additive.ofMul value = Additive.ofMul value
    exact one_zsmul _
  rw [integerInRational_one, integerMap_one] at atOne
  change
    (CategoryTheory.Injective.factorThru
      integerMap integerInRational).hom (ULift.up (1 : ℚ)) =
        Additive.ofMul value at atOne
  exact atOne

namespace CompatibleRootSystem

noncomputable def ofRootable
    {B : Type u} [CommGroup B] [RootableBy B ℕ]
    (value : B) : CompatibleRootSystem B value where
  roots := rootableRationalPowers value
  root_one := rootableRationalPowers_one value

end CompatibleRootSystem

namespace AlgebraicClosureRootSystem

variable {K : Type u} [Field K] [IsAlgClosed K]

@[implicit_reducible]
noncomputable def unitsRootableByNat : RootableBy Kˣ ℕ :=
  rootableByOfPowLeftSurj _ _ fun {n} hn value =>
    exists_pow_root value n hn

noncomputable def compatibleRationalRoots (value : Kˣ) :
    CompatibleRootSystem Kˣ value := by
  letI : RootableBy Kˣ ℕ := unitsRootableByNat
  exact CompatibleRootSystem.ofRootable value

end AlgebraicClosureRootSystem

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def rationalRootSystem : Obligation :=
  { id := "IUT-II.compatible-rational-roots-from-divisibility"
    source := "IUT II Kummer root layer; Absolute Anabelian Topics III, Proposition 3.2(ii)"
    status := VerificationStatus.proved
    note :=
      "Divisibility of a commutative group is converted into one compatible " ++
        "rational-power homomorphism by extending Z -> B across Z -> Q. " ++
        "Algebraically closed field units instantiate the construction. No " ++
        "unrelated per-degree choices or Kummer-isomorphism existence claim is used."
    dependsOn := ["IUT-II.natural-compatible-root-system"] }

end LeanFormal.IUT.Audit
