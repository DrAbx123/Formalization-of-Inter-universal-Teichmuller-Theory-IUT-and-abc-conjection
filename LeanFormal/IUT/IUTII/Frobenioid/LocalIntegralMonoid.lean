import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.ValuativeRel
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Filtration
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

open scoped nonZeroDivisors

/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
  The local arithmetic carrier underlying the Frobenioid evaluation.

  For a rational prime `p`, `LocalAlgebraicIntegerRing p` is the integral
  closure of the valuation ring of `Q_p` in its algebraic closure, and
  `LocalIntegralMonoid p` is its nonzero multiplicative monoid.  This is the
  literal `O_(Kbar)^triangle` carrier used by the source; no arbitrary type or
  existence field is introduced.
-/

namespace LeanFormal.IUT

noncomputable abbrev LocalAlgebraicIntegerRing
    (p : Nat) [Fact (Nat.Prime p)] : Type :=
  integralClosure
    (Valuation.integer (ValuativeRel.valuation ℚ_[p]))
    (AlgebraicClosure ℚ_[p])

noncomputable abbrev LocalIntegralMonoid
    (p : Nat) [Fact (Nat.Prime p)] : Type :=
  (LocalAlgebraicIntegerRing p)⁰

namespace LocalIntegralMonoid

variable (p : Nat) [Fact (Nat.Prime p)]

noncomputable def integralClosureAlgEquiv
    (sigma : LocalAbsoluteGalois p) :
    LocalAlgebraicIntegerRing p ≃+* LocalAlgebraicIntegerRing p :=
  ((sigma.restrictScalars
    (Valuation.integer (ValuativeRel.valuation ℚ_[p]))).mapIntegralClosure).toRingEquiv

noncomputable def galoisMulAut
    (sigma : LocalAbsoluteGalois p) :
    MulAut (LocalIntegralMonoid p) where
  toFun value :=
    ⟨integralClosureAlgEquiv p sigma value.1,
      mem_nonZeroDivisors_of_ne_zero (by
        rw [← map_zero (integralClosureAlgEquiv p sigma)]
        exact (integralClosureAlgEquiv p sigma).injective.ne
          (nonZeroDivisors.coe_ne_zero value))⟩
  invFun value :=
    ⟨integralClosureAlgEquiv p sigma.symm value.1,
      mem_nonZeroDivisors_of_ne_zero (by
        rw [← map_zero (integralClosureAlgEquiv p sigma.symm)]
        exact (integralClosureAlgEquiv p sigma.symm).injective.ne
          (nonZeroDivisors.coe_ne_zero value))⟩
  left_inv value := by
    apply Subtype.ext
    apply Subtype.ext
    exact sigma.left_inv value.1.1
  right_inv value := by
    apply Subtype.ext
    apply Subtype.ext
    exact sigma.right_inv value.1.1
  map_mul' first second := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul sigma first.1.1 second.1.1

noncomputable def galoisAction :
    LocalAbsoluteGalois p →* MulAut (LocalIntegralMonoid p) where
  toFun := galoisMulAut p
  map_one' := by
    apply MulEquiv.ext
    intro value
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' first second := by
    apply MulEquiv.ext
    intro value
    apply Subtype.ext
    apply Subtype.ext
    rfl

noncomputable def openStabilizer
    (value : LocalIntegralMonoid p) : OpenSubgroup (LocalAbsoluteGalois p) := by
  change OpenSubgroup
    ((AlgebraicClosure ℚ_[p]) ≃ₐ[ℚ_[p]] (AlgebraicClosure ℚ_[p]))
  exact
    ⟨MulAction.stabilizer
        ((AlgebraicClosure ℚ_[p]) ≃ₐ[ℚ_[p]] (AlgebraicClosure ℚ_[p]))
        value.1.1,
      stabilizer_isOpen_of_isIntegral value.1.1⟩

theorem openStabilizer_fixed
    (value : LocalIntegralMonoid p)
    (g : openStabilizer p value) :
    galoisAction p (g : LocalAbsoluteGalois p) value = value := by
  apply Subtype.ext
  apply Subtype.ext
  exact g.property

noncomputable def toAlgebraicClosureUnits :
    LocalIntegralMonoid p →* (AlgebraicClosure ℚ_[p])ˣ where
  toFun value :=
    Units.mk0 value.1.1
      (fun equality =>
        nonZeroDivisors.coe_ne_zero value (Subtype.ext equality))
  map_one' := by
    apply Units.ext
    rfl
  map_mul' first second := by
    apply Units.ext
    rfl

noncomputable def groupificationToAlgebraicClosureUnits :
    Algebra.GrothendieckGroup (LocalIntegralMonoid p) →*
      (AlgebraicClosure ℚ_[p])ˣ :=
  Algebra.GrothendieckGroup.lift (toAlgebraicClosureUnits p)

@[simp]
theorem groupificationToAlgebraicClosureUnits_of
    (value : LocalIntegralMonoid p) :
    groupificationToAlgebraicClosureUnits p
        (Algebra.GrothendieckGroup.of value) =
      toAlgebraicClosureUnits p value := by
  let universalProperty :=
    Equiv.symm_apply_apply
      (Algebra.GrothendieckGroup.lift
        (M := LocalIntegralMonoid p)
        (G := (AlgebraicClosure ℚ_[p])ˣ))
      (toAlgebraicClosureUnits p)
  change
    (Algebra.GrothendieckGroup.lift
        (toAlgebraicClosureUnits p)).comp
          Algebra.GrothendieckGroup.of =
      toAlgebraicClosureUnits p at universalProperty
  exact DFunLike.congr_fun universalProperty value

theorem algebraicClosure_isFractionRing :
    IsFractionRing
      (LocalAlgebraicIntegerRing p)
      (AlgebraicClosure ℚ_[p]) := by
  let baseRing := Valuation.integer (ValuativeRel.valuation ℚ_[p])
  letI : Algebra.IsAlgebraic baseRing (AlgebraicClosure ℚ_[p]) :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance : Algebra.IsAlgebraic ℚ_[p]
        (AlgebraicClosure ℚ_[p]))
  exact
    integralClosure.isFractionRing_of_algebraic
      (fun value equality => by
        apply Subtype.ext
        change (value : ℚ_[p]) = 0
        apply (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective
        change algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])
            (value : ℚ_[p]) = 0 at equality
        simpa only [map_zero] using equality)

theorem grothendieckLift_injective
    {M B : Type u} [CommMonoid M] [CommGroup B]
    (hom : M →* B) (hom_injective : Function.Injective hom) :
    Function.Injective
      (Algebra.GrothendieckGroup.lift hom) := by
  letI : IsCancelMul M :=
    hom_injective.isCancelMul hom (map_mul hom)
  change Function.Injective
    ((Localization.monoidOf (⊤ : Submonoid M)).lift
      (fun _ => Group.isUnit _))
  rw [Submonoid.LocalizationMap.lift_injective_iff]
  intro first second
  constructor
  · intro equality
    exact congrArg hom (Algebra.GrothendieckGroup.of_injective equality)
  · intro equality
    exact congrArg Algebra.GrothendieckGroup.of
      (hom_injective equality)

theorem groupificationToAlgebraicClosureUnits_surjective :
    Function.Surjective (groupificationToAlgebraicClosureUnits p) := by
  letI : IsFractionRing
      (LocalAlgebraicIntegerRing p) (AlgebraicClosure ℚ_[p]) :=
    algebraicClosure_isFractionRing p
  intro value
  obtain ⟨numerator, denominator, denominatorRegular, quotient_eq⟩ :=
    IsFractionRing.div_surjective
      (LocalAlgebraicIntegerRing p) (value : AlgebraicClosure ℚ_[p])
  have numerator_ne_zero : numerator ≠ 0 := by
    intro equality
    subst numerator
    have value_eq_zero : (value : AlgebraicClosure ℚ_[p]) = 0 := by
      simpa using quotient_eq.symm
    exact value.ne_zero value_eq_zero
  let numeratorMonoid : LocalIntegralMonoid p :=
    ⟨numerator,
      mem_nonZeroDivisors_iff_ne_zero.mpr numerator_ne_zero⟩
  let denominatorMonoid : LocalIntegralMonoid p :=
    ⟨denominator, denominatorRegular⟩
  refine
    ⟨Algebra.GrothendieckGroup.of numeratorMonoid /
        Algebra.GrothendieckGroup.of denominatorMonoid, ?_⟩
  rw [map_div, groupificationToAlgebraicClosureUnits_of,
    groupificationToAlgebraicClosureUnits_of]
  apply Units.ext
  exact quotient_eq

theorem groupificationToAlgebraicClosureUnits_injective :
    Function.Injective (groupificationToAlgebraicClosureUnits p) :=
  grothendieckLift_injective
    (toAlgebraicClosureUnits p) (by
      intro first second equality
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg Units.val equality)

noncomputable def groupificationEquivAlgebraicClosureUnits :
    Algebra.GrothendieckGroup (LocalIntegralMonoid p) ≃*
      (AlgebraicClosure ℚ_[p])ˣ :=
  MulEquiv.ofBijective
    (groupificationToAlgebraicClosureUnits p)
    ⟨groupificationToAlgebraicClosureUnits_injective p,
      groupificationToAlgebraicClosureUnits_surjective p⟩

noncomputable def unitActionMulAut
    (g : LocalAbsoluteGalois p) :
    MulAut (LocalIntegralMonoid p)ˣ :=
  Units.mapEquiv (galoisAction p g)

noncomputable def unitAction :
    LocalAbsoluteGalois p →* MulAut (LocalIntegralMonoid p)ˣ where
  toFun := unitActionMulAut p
  map_one' := by
    apply MulEquiv.ext
    intro unit
    apply Units.ext
    simp [unitActionMulAut]
  map_mul' first second := by
    apply MulEquiv.ext
    intro unit
    apply Units.ext
    simp [unitActionMulAut]

noncomputable def unitEvaluation :
    (LocalIntegralMonoid p)ˣ →* (AlgebraicClosure ℚ_[p])ˣ :=
  { toFun := fun unit =>
      Units.mk0 (unit.val.1.1)
        (by
          have hlocal : unit.val.1 ≠ 0 := by
            intro equality
            apply nonZeroDivisors.coe_ne_zero unit.val
            exact equality
          intro equality
          apply hlocal
          apply Subtype.ext
          exact equality)
    map_one' := by
      apply Units.ext
      rfl
    map_mul' := by
      intro first second
      apply Units.ext
      rfl }

theorem unitEvaluation_equivariant
    (g : LocalAbsoluteGalois p) (unit : (LocalIntegralMonoid p)ˣ) :
    unitEvaluation p (unitAction p g unit) =
      localGaloisUnitsAction p g (unitEvaluation p unit) := by
  apply Units.ext
  rfl

end LocalIntegralMonoid

namespace Audit

def localIntegralMonoid : Obligation :=
  { id := "IUT-II.local-integral-monoid-carrier"
    source := "IUT II, Definition 4.9(i); Absolute Anabelian Topics III, Definition 3.1(i)"
    status := VerificationStatus.proved
    note :=
      "The integral closure of the Q_p valuation ring in its algebraic closure " ++
        "and its nonzero multiplicative monoid are actual Mathlib carriers. " ++
        "The Galois action, its open stabilizer, and fixedness are proved. The " ++
        "fraction-ring theorem identifies the Grothendieck groupification with " ++
        "the units of the algebraic closure, and the unit evaluation is proved " ++
        "Galois-equivariant. " ++
        "The universal-cover pro-object and the full Frobenioid evaluation functor " ++
        "remain separate obligations."
    dependsOn := ["IUT-I-II.local-prime-place-carrier"] }

end Audit

end LeanFormal.IUT
