import Iut.Foundations.SourceThetaEvaluation

open CategoryTheory

namespace Iut

universe u

namespace SourceSplitKummerMonoid

variable {M : Type u} [CommMonoid M]

/--
Multiplication of the full unit group with a proposed characteristic factor.
-/
def unitCharacteristicMultiplication (S : Submonoid M) :
    Mˣ × S → M :=
  fun pair => (pair.1 : M) * pair.2.1

/--
A characteristic factor has no nontrivial units when unit-characteristic
multiplication is injective.
-/
theorem characteristic_eq_one_of_isUnit
    (S : Submonoid M)
    (hinjective : Function.Injective (unitCharacteristicMultiplication S))
    (value : S) (hvalue : IsUnit (value.1 : M)) :
    value = 1 := by
  let unit : Mˣ := hvalue.unit
  have hunit : (unit : M) = value.1 := hvalue.unit_spec
  have heq :
      unitCharacteristicMultiplication S (unit, 1) =
        unitCharacteristicMultiplication S (1, value) := by
    change (unit : M) * 1 = 1 * value.1
    simp [hunit]
  exact (congrArg Prod.snd (hinjective heq)).symm

/-- A subgroup of ambient units, embedded as units of any submonoid containing it. -/
noncomputable def subgroupUnits
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S) : H →* Sˣ where
  toFun unit :=
    { val := ⟨(unit.1 : M),
        hH (H.mem_ofUnits unit.2 rfl)⟩
      inv := ⟨((unit.1⁻¹ : Mˣ) : M),
        hH (H.mem_ofUnits (H.inv_mem unit.2) rfl)⟩
      val_inv := by
        apply Subtype.ext
        simp
      inv_val := by
        apply Subtype.ext
        simp }
  map_one' := by ext; rfl
  map_mul' first second := by ext; rfl

/-- The exact congruence identifying multiplication by a selected unit subgroup. -/
noncomputable def unitCongruence
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S) : Con S where
  r first second :=
    ∃ unit : H,
      first = (subgroupUnits S H hH unit : S) * second
  iseqv := by
    constructor
    · intro value
      exact ⟨1, by simp⟩
    · intro first second h
      rcases h with ⟨unit, rfl⟩
      refine ⟨unit⁻¹, ?_⟩
      simp
    · intro first second third hfirst hsecond
      rcases hfirst with ⟨firstUnit, rfl⟩
      rcases hsecond with ⟨secondUnit, rfl⟩
      refine ⟨firstUnit * secondUnit, ?_⟩
      simp [mul_assoc]
  mul' := by
    intro first second third fourth hfirst hsecond
    rcases hfirst with ⟨firstUnit, rfl⟩
    rcases hsecond with ⟨secondUnit, rfl⟩
    refine ⟨firstUnit * secondUnit, ?_⟩
    simp [mul_assoc, mul_comm, mul_left_comm]

/-- A commutative monoid modulo a specified subgroup of its ambient units. -/
abbrev UnitQuotient
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S) :=
  (unitCongruence S H hH).Quotient

theorem unitQuotient_mk_eq_iff
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S) (first second : S) :
    (first : UnitQuotient S H hH) = second ↔
      ∃ unit : H,
        first = (subgroupUnits S H hH unit : S) * second := by
  exact (unitCongruence S H hH).eq

theorem unitQuotient_mk_subgroupUnit_eq_one
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S) (unit : H) :
    ((subgroupUnits S H hH unit : S) :
      UnitQuotient S H hH) = 1 := by
  apply (unitCongruence S H hH).eq.mpr
  exact ⟨unit, by simp⟩

variable [IsCancelMul M]

/-- Quotienting `H · S` by `H` leaves no units when `S` is characteristic. -/
theorem unitQuotient_isUnit_eq_one
    (characteristic : Submonoid M)
    (H : Subgroup Mˣ)
    (hinjective :
      Function.Injective
        (unitCharacteristicMultiplication characteristic))
    (value : UnitQuotient
      (H.ofUnits ⊔ characteristic) H le_sup_left)
    (hvalue : IsUnit value) :
    value = 1 := by
  let generated := H.ofUnits ⊔ characteristic
  let inclusion : H.ofUnits ≤ generated := le_sup_left
  induction value using Con.induction_on with
  | _ representative =>
    let inverseValue : UnitQuotient generated H inclusion :=
      (hvalue.unit⁻¹ : (UnitQuotient generated H inclusion)ˣ)
    obtain ⟨inverseRepresentative, hinverseRepresentative⟩ :=
      (unitCongruence generated H inclusion).mk'_surjective inverseValue
    have hproduct :
        ((representative * inverseRepresentative : generated) :
            UnitQuotient generated H inclusion) = 1 := by
      change
        (representative : UnitQuotient generated H inclusion) *
            (inverseRepresentative : UnitQuotient generated H inclusion) = 1
      have hinverse :
          (inverseRepresentative : UnitQuotient generated H inclusion) =
            inverseValue := hinverseRepresentative
      rw [hinverse]
      rw [← hvalue.unit_spec]
      simp [inverseValue]
    have hproductRelation :=
      (unitCongruence generated H inclusion).eq.mp hproduct
    rcases hproductRelation with ⟨productUnit, hproduct⟩
    rcases (Submonoid.mem_sup.mp representative.2) with
      ⟨firstUnitValue, hfirstUnitValue,
        firstCharacteristic, hfirstCharacteristic, hfirst⟩
    rcases (Submonoid.mem_sup.mp inverseRepresentative.2) with
      ⟨secondUnitValue, hsecondUnitValue,
        secondCharacteristic, hsecondCharacteristic, hsecond⟩
    let firstUnit : H :=
      ⟨H.unit_of_mem_ofUnits hfirstUnitValue,
        H.unit_of_mem_ofUnits_spec_mem⟩
    let secondUnit : H :=
      ⟨H.unit_of_mem_ofUnits hsecondUnitValue,
        H.unit_of_mem_ofUnits_spec_mem⟩
    have hcharacteristicProductIsUnit :
        IsUnit (firstCharacteristic * secondCharacteristic : M) := by
      let resultingUnit : Mˣ :=
        (firstUnit.1 * secondUnit.1)⁻¹ * productUnit.1
      refine ⟨resultingUnit, ?_⟩
      change
        (resultingUnit : M) =
          firstCharacteristic * secondCharacteristic
      apply mul_left_cancel
        (a := ((firstUnit.1 * secondUnit.1 : Mˣ) : M))
      change
        ((firstUnit.1 * secondUnit.1 : Mˣ) : M) *
            (resultingUnit : M) =
          ((firstUnit.1 * secondUnit.1 : Mˣ) : M) *
            (firstCharacteristic * secondCharacteristic)
      rw [show
        ((firstUnit.1 * secondUnit.1 : Mˣ) : M) *
            (resultingUnit : M) = (productUnit.1 : M) by
          rw [← Units.val_mul]
          apply congrArg Units.val
          change
            (firstUnit.1 * secondUnit.1) *
                ((firstUnit.1 * secondUnit.1)⁻¹ * productUnit.1) =
              productUnit.1
          simp [mul_assoc]]
      have hproductVal :
          representative.1 * inverseRepresentative.1 =
            (productUnit.1 : M) := by
        simpa using congrArg Subtype.val hproduct
      rw [← hproductVal, ← hfirst, ← hsecond]
      change
        (firstUnit.1 : M) * firstCharacteristic *
              ((secondUnit.1 : M) * secondCharacteristic) =
          ((firstUnit.1 * secondUnit.1 : Mˣ) : M) *
            (firstCharacteristic * secondCharacteristic)
      simp only [Units.val_mul]
      ac_rfl
    have hfirstCharacteristicIsUnit :
        IsUnit (firstCharacteristic : M) :=
      (IsUnit.mul_iff.mp hcharacteristicProductIsUnit).1
    have hfirstCharacteristicEq :
        (⟨firstCharacteristic, hfirstCharacteristic⟩ : characteristic) = 1 :=
      characteristic_eq_one_of_isUnit characteristic hinjective
        ⟨firstCharacteristic, hfirstCharacteristic⟩
        hfirstCharacteristicIsUnit
    apply (unitCongruence generated H inclusion).eq.mpr
    refine ⟨firstUnit, ?_⟩
    apply Subtype.ext
    change representative.1 = (firstUnit.1 : M) * 1
    rw [← hfirst]
    have : firstCharacteristic = 1 := congrArg Subtype.val hfirstCharacteristicEq
    rw [this, mul_one, mul_one]
    exact
      (H.unit_of_mem_ofUnits_spec_val_eq_of_mem
        hfirstUnitValue).symm

/-- If the first factor has only the identity unit, the units of a product are the second group. -/
noncomputable def productUnitsEquivSecond
    (Q U : Type u) [CommMonoid Q] [CommGroup U]
    (hQ : ∀ value : Q, IsUnit value → value = 1) :
    (Q × U)ˣ ≃* U where
  toFun unit := (MulEquiv.prodUnits unit).2
  invFun value := MulEquiv.prodUnits.symm (1, toUnits value)
  left_inv unit := by
    apply MulEquiv.prodUnits.injective
    apply Prod.ext
    · apply Units.ext
      exact (hQ _ (MulEquiv.prodUnits unit).1.isUnit).symm
    · simp
  right_inv value := by
    simp
  map_mul' first second := by
    simp

end SourceSplitKummerMonoid

namespace SourceMLFGaloisTMPair

variable {G : TopologicalGroupCat.{u}}

/-- The positive integer `2 * ell` used at a bad finite place. -/
def twoEll (l : PrimeGeFive) : ℕ+ :=
  ⟨2 * l.value, Nat.mul_pos (by decide) l.prime.pos⟩

/-- The literal group `mu_(2 ell)(A)`. -/
abbrev TwoEllRootsOfUnity
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive) :=
  pair.arithmeticMonoid.RootsOfUnityGroup (twoEll l)

/-- `O^perp(A)`: generated by `mu_(2 ell)(A)` and the splitting image. -/
abbrev badPerpMonoid
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier) :=
  (pair.arithmeticMonoid.rootsOfUnitySubgroup (twoEll l)).ofUnits ⊔
    characteristic

/-- `O^square(A) = O^perp(A) / mu_(2 ell)(A)` at a bad finite place. -/
abbrev badCharacteristicQuotient
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier) :=
  SourceSplitKummerMonoid.UnitQuotient
    (badPerpMonoid pair l characteristic)
    (pair.arithmeticMonoid.rootsOfUnitySubgroup (twoEll l))
    le_sup_left

/-- The direct product monoid `O^(square times-mu)(A)` at a bad finite place. -/
abbrev badTimesMuMonoid
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier) :=
  badCharacteristicQuotient pair l characteristic ×
    pair.UnitModuloTorsion

/-- The direct product monoid `O^(square times-mu)(A)` at a good finite place. -/
abbrev goodTimesMuMonoid
    (pair : SourceMLFGaloisTMPair G)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier) :=
  characteristic × pair.UnitModuloTorsion

/-- At a bad place, the complete unit group of `O^(square times-mu)` is `O^(times-mu)`. -/
noncomputable def badTimesMuUnitsEquiv
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier)
    (hinjective : Function.Injective
      (SourceSplitKummerMonoid.unitCharacteristicMultiplication
        characteristic)) :
    (pair.badTimesMuMonoid l characteristic)ˣ ≃*
      pair.UnitModuloTorsion :=
  SourceSplitKummerMonoid.productUnitsEquivSecond _ _ fun value hvalue =>
    SourceSplitKummerMonoid.unitQuotient_isUnit_eq_one characteristic
      (pair.arithmeticMonoid.rootsOfUnitySubgroup (twoEll l))
      hinjective value hvalue

/-- At a good place, the complete unit group of `O^(square times-mu)` is `O^(times-mu)`. -/
noncomputable def goodTimesMuUnitsEquiv
    (pair : SourceMLFGaloisTMPair G)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier)
    (hinjective : Function.Injective
      (SourceSplitKummerMonoid.unitCharacteristicMultiplication
        characteristic)) :
    (pair.goodTimesMuMonoid characteristic)ˣ ≃*
      pair.UnitModuloTorsion :=
  SourceSplitKummerMonoid.productUnitsEquivSecond _ _ fun value hvalue => by
    exact SourceSplitKummerMonoid.characteristic_eq_one_of_isUnit
      characteristic hinjective value
      (hvalue.map characteristic.subtype)

end SourceMLFGaloisTMPair

/-!
## Finite-place split `times-mu` Kummer Frobenioids

The preceding constructions give the literal monoids and their Galois
actions.  The records below state the remaining Frobenioid reconstruction
boundary of IUT II, Definition 4.9(ii)--(iv), without replacing it by an
unrelated carrier type.
-/

/-- The two finite-place cases of IUT II, Definition 4.9(ii)--(iv). -/
inductive SourceFiniteTimesMuPlaceKind
  | bad
  | good
  deriving DecidableEq

/--
The exact input from a split `F^\vdash` Frobenioid at one finite place.

The rational monoid at the selected universal-cover reference object is
identified with the arithmetic monoid of an actual MLF-Galois `TM` pair.  The
selected characteristic splitting is transported to a stable submonoid, and
the `times-mu` Kummer structure is the genuine `Ism` orbit of Definition
4.9(i), not a proposition recording that some Kummer map exists.
-/
structure SourceFiniteTimesMuKummerInput
    (ell : PrimeGeFive)
    (underlying : SplitFrobenioidPresentation.{u}) where
  kind : SourceFiniteTimesMuPlaceKind
  referenceObject : underlying.frobenioid.carrier
  referenceObject_isotropic :
    underlying.frobenioid.preFrobenioid.IsIsotropic referenceObject
  selectedSplitting : underlying.splittingIndex
  galoisGroup : TopologicalGroupCat.{u}
  groupPair : SourceMLFGaloisTMPair galoisGroup
  coverPair : SourceMLFGaloisTMPair galoisGroup
  rationalMonoidIso :
    underlying.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
        referenceObject ≃*
      coverPair.arithmeticMonoid.carrier
  characteristic : Submonoid coverPair.arithmeticMonoid.carrier
  characteristic_eq_splitting :
    ∀ value :
        underlying.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
          referenceObject,
      value ∈
          (underlying.splitting selectedSplitting).tau
            { obj := referenceObject
              isotropic := referenceObject_isotropic } ↔
        rationalMonoidIso value ∈ characteristic
  characteristic_stable :
    ∀ g value,
      value ∈ characteristic →
        coverPair.action g value ∈ characteristic
  unit_characteristic_injective :
    Function.Injective
      (SourceSplitKummerMonoid.unitCharacteristicMultiplication
        characteristic)
  kummerStructure :
    SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.TimesMuKummerOrbit
      groupPair coverPair

namespace SourceFiniteTimesMuKummerInput

/--
The literal `O^(square times-mu)` monoid dictated by the place kind: quotient
by `mu_(2 ell)` at a bad place and the unquotiented characteristic factor at a
good place.
-/
abbrev timesMuMonoid
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (input : SourceFiniteTimesMuKummerInput ell underlying) : Type u :=
  match input.kind with
  | .bad =>
      input.coverPair.badTimesMuMonoid ell input.characteristic
  | .good =>
      input.coverPair.goodTimesMuMonoid input.characteristic

noncomputable instance timesMuMonoidCommMonoid
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (input : SourceFiniteTimesMuKummerInput ell underlying) :
    CommMonoid input.timesMuMonoid := by
  rcases input with
    ⟨kind, referenceObject, referenceObject_isotropic,
      selectedSplitting, galoisGroup, groupPair, coverPair,
      rationalMonoidIso, characteristic, characteristic_eq_splitting,
      characteristic_stable, unit_characteristic_injective,
      kummerStructure⟩
  cases kind with
  | bad => infer_instance
  | good => infer_instance

/-- The complete unit group of the reconstructed monoid is `O^(times-mu)`. -/
noncomputable def timesMuUnitsEquiv
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (input : SourceFiniteTimesMuKummerInput ell underlying) :
    input.timesMuMonoidˣ ≃* input.coverPair.UnitModuloTorsion := by
  rcases input with
    ⟨kind, referenceObject, referenceObject_isotropic,
      selectedSplitting, galoisGroup, groupPair, coverPair,
      rationalMonoidIso, characteristic, characteristic_eq_splitting,
      characteristic_stable, unit_characteristic_injective,
      kummerStructure⟩
  cases kind with
  | bad =>
      exact coverPair.badTimesMuUnitsEquiv ell characteristic
        unit_characteristic_injective
  | good =>
      exact coverPair.goodTimesMuUnitsEquiv characteristic
        unit_characteristic_injective

end SourceFiniteTimesMuKummerInput

/--
The output of the model-Frobenioid reconstruction in Definition 4.9(iii)-(iv).

Its reference rational monoid is identified with the monoid constructed from
the input, and its base category is the base category of the original split
Frobenioid.  Thus this record cannot be inhabited merely by choosing an
unrelated split Frobenioid.
-/
structure SourceFiniteTimesMuKummerFrobenioid
    (ell : PrimeGeFive)
    (underlying : SplitFrobenioidPresentation.{u}) where
  input : SourceFiniteTimesMuKummerInput ell underlying
  reconstructed : SplitFrobenioidPresentation.{u}
  referenceObject : reconstructed.frobenioid.carrier
  referenceObject_isotropic :
    reconstructed.frobenioid.preFrobenioid.IsIsotropic referenceObject
  rationalMonoidIso :
    reconstructed.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
        referenceObject ≃*
      input.timesMuMonoid
  baseEquivalence :
    CategoryTheory.Equivalence
      reconstructed.frobenioid.baseCategory
      underlying.frobenioid.baseCategory

namespace SourceFiniteTimesMuKummerFrobenioid

/-- The reconstructed rational monoid has exactly the required `times-mu` units. -/
noncomputable def rationalUnitsEquiv
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (output : SourceFiniteTimesMuKummerFrobenioid ell underlying) :
    (output.reconstructed.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
        output.referenceObject)ˣ ≃*
      output.input.coverPair.UnitModuloTorsion :=
  (Units.mapEquiv output.rationalMonoidIso).trans
    output.input.timesMuUnitsEquiv

end SourceFiniteTimesMuKummerFrobenioid

namespace SourceSplitKummerMonoid

variable {M : Type u} [CommMonoid M]

/-- A monoid automorphism preserving the quotienting subgroup descends to the unit quotient. -/
noncomputable def unitQuotientMapHom
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S)
    (automorphism : MulAut S)
    (subgroupAutomorphism : MulAut H)
    (compatible : ∀ unit,
      automorphism (subgroupUnits S H hH unit : S) =
        (subgroupUnits S H hH (subgroupAutomorphism unit) : S)) :
    UnitQuotient S H hH →* UnitQuotient S H hH := by
  let congruence := unitCongruence S H hH
  apply congruence.lift
    (congruence.mk'.comp automorphism.toMonoidHom)
  intro first second hrelation
  apply congruence.eq.mpr
  rcases hrelation with ⟨unit, hrelation⟩
  refine ⟨subgroupAutomorphism unit, ?_⟩
  rw [← compatible]
  simpa only [map_mul] using congrArg automorphism hrelation

@[simp]
theorem unitQuotientMapHom_mk
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S)
    (automorphism : MulAut S)
    (subgroupAutomorphism : MulAut H)
    (compatible : ∀ unit,
      automorphism (subgroupUnits S H hH unit : S) =
        (subgroupUnits S H hH (subgroupAutomorphism unit) : S))
    (value : S) :
    unitQuotientMapHom S H hH automorphism subgroupAutomorphism compatible value =
      (automorphism value : UnitQuotient S H hH) :=
  by simp [unitQuotientMapHom]

/-- The descended map is an automorphism of the exact unit quotient. -/
noncomputable def unitQuotientMulAut
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S)
    (automorphism : MulAut S)
    (subgroupAutomorphism : MulAut H)
    (compatible : ∀ unit,
      automorphism (subgroupUnits S H hH unit : S) =
        (subgroupUnits S H hH (subgroupAutomorphism unit) : S)) :
    MulAut (UnitQuotient S H hH) where
  toFun := unitQuotientMapHom S H hH automorphism
    subgroupAutomorphism compatible
  invFun := unitQuotientMapHom S H hH automorphism.symm
    subgroupAutomorphism.symm (by
      intro unit
      apply automorphism.injective
      rw [automorphism.apply_symm_apply]
      rw [compatible]
      rw [subgroupAutomorphism.apply_symm_apply])
  left_inv value := by
    induction value using Con.induction_on with
    | _ representative =>
      rw [unitQuotientMapHom_mk, unitQuotientMapHom_mk]
      rw [automorphism.symm_apply_apply]
  right_inv value := by
    induction value using Con.induction_on with
    | _ representative =>
      rw [unitQuotientMapHom_mk, unitQuotientMapHom_mk]
      rw [automorphism.apply_symm_apply]
  map_mul' := map_mul
    (unitQuotientMapHom S H hH automorphism
      subgroupAutomorphism compatible)

@[simp]
theorem unitQuotientMulAut_mk
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S)
    (automorphism : MulAut S)
    (subgroupAutomorphism : MulAut H)
    (compatible : ∀ unit,
      automorphism (subgroupUnits S H hH unit : S) =
        (subgroupUnits S H hH (subgroupAutomorphism unit) : S))
    (value : S) :
    unitQuotientMulAut S H hH automorphism subgroupAutomorphism compatible value =
      (automorphism value : UnitQuotient S H hH) :=
  by
    exact unitQuotientMapHom_mk S H hH automorphism
      subgroupAutomorphism compatible value

/-- Compatible actions on a monoid and its selected units descend to the quotient. -/
noncomputable def unitQuotientAction
    {Acting : Type u} [Group Acting]
    (S : Submonoid M) (H : Subgroup Mˣ)
    (hH : H.ofUnits ≤ S)
    (monoidAction : Acting →* MulAut S)
    (subgroupAction : Acting →* MulAut H)
    (compatible : ∀ g unit,
      monoidAction g (subgroupUnits S H hH unit : S) =
        (subgroupUnits S H hH (subgroupAction g unit) : S)) :
    Acting →* MulAut (UnitQuotient S H hH) where
  toFun g := unitQuotientMulAut S H hH
    (monoidAction g) (subgroupAction g) (compatible g)
  map_one' := by
    apply MulEquiv.ext
    intro value
    induction value using Con.induction_on with
    | _ representative =>
      rw [unitQuotientMulAut_mk]
      change ((monoidAction 1 representative : S) :
        UnitQuotient S H hH) = representative
      rw [map_one]
      rfl
  map_mul' first second := by
    apply MulEquiv.ext
    intro value
    induction value using Con.induction_on with
    | _ representative =>
      change
        unitQuotientMulAut S H hH
            (monoidAction (first * second))
            (subgroupAction (first * second))
            (compatible (first * second)) representative =
          unitQuotientMulAut S H hH
            (monoidAction first) (subgroupAction first)
            (compatible first)
            (unitQuotientMulAut S H hH
              (monoidAction second) (subgroupAction second)
              (compatible second) representative)
      rw [unitQuotientMulAut_mk, unitQuotientMulAut_mk,
        unitQuotientMulAut_mk]
      change ((monoidAction (first * second) representative : S) :
          UnitQuotient S H hH) =
        ((monoidAction first (monoidAction second representative) : S) :
          UnitQuotient S H hH)
      rw [map_mul]
      rfl

/-- The componentwise product of two genuine multiplicative actions. -/
def productAction
    {Acting Q U : Type u} [Group Acting]
    [CommMonoid Q] [CommMonoid U]
    (first : Acting →* MulAut Q)
    (second : Acting →* MulAut U) :
    Acting →* MulAut (Q × U) where
  toFun g := (first g).prodCongr (second g)
  map_one' := by
    apply MulEquiv.ext
    rintro ⟨q, u⟩
    apply Prod.ext
    · change first 1 q = q
      rw [map_one]
      rfl
    · change second 1 u = u
      rw [map_one]
      rfl
  map_mul' left right := by
    apply MulEquiv.ext
    rintro ⟨q, u⟩
    apply Prod.ext
    · change first (left * right) q = first left (first right q)
      rw [map_mul]
      rfl
    · change second (left * right) u = second left (second right u)
      rw [map_mul]
      rfl

end SourceSplitKummerMonoid

namespace SourceMLFGaloisTMPair

variable {G : TopologicalGroupCat.{u}}

/-- Restrict one ambient Galois automorphism to a stable submonoid. -/
def stableSubmonoidActionMulAut
    (pair : SourceMLFGaloisTMPair G)
    (S : Submonoid pair.arithmeticMonoid.carrier)
    (stable : ∀ g value, value ∈ S → pair.action g value ∈ S)
    (g : G) : MulAut S where
  toFun value := ⟨pair.action g value.1, stable g value.1 value.2⟩
  invFun value := ⟨pair.action g⁻¹ value.1, stable g⁻¹ value.1 value.2⟩
  left_inv value := by
    apply Subtype.ext
    change pair.action g⁻¹ (pair.action g value.1) = value.1
    rw [map_inv]
    exact (pair.action g).symm_apply_apply value.1
  right_inv value := by
    apply Subtype.ext
    change pair.action g (pair.action g⁻¹ value.1) = value.1
    rw [map_inv]
    exact (pair.action g).apply_symm_apply value.1
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul (pair.action g) first.1 second.1

/-- The restricted automorphisms form the Galois action on a stable submonoid. -/
def stableSubmonoidAction
    (pair : SourceMLFGaloisTMPair G)
    (S : Submonoid pair.arithmeticMonoid.carrier)
    (stable : ∀ g value, value ∈ S → pair.action g value ∈ S) :
    G →* MulAut S where
  toFun := pair.stableSubmonoidActionMulAut S stable
  map_one' := by
    apply MulEquiv.ext
    intro value
    apply Subtype.ext
    simp [stableSubmonoidActionMulAut]
  map_mul' first second := by
    apply MulEquiv.ext
    intro value
    apply Subtype.ext
    simp [stableSubmonoidActionMulAut]

/-- Every Galois automorphism preserves the subgroup of `n`-th roots. -/
theorem unitAction_mem_rootsOfUnity_iff
    (pair : SourceMLFGaloisTMPair G) (n : ℕ+)
    (g : G) (unit : pair.arithmeticMonoid.carrierˣ) :
    pair.unitActionMulAut g unit ∈
        pair.arithmeticMonoid.rootsOfUnitySubgroup n ↔
      unit ∈ pair.arithmeticMonoid.rootsOfUnitySubgroup n := by
  change (pair.unitActionMulAut g unit) ^ n.val = 1 ↔ unit ^ n.val = 1
  constructor
  · intro h
    apply (pair.unitActionMulAut g).injective
    rw [map_pow, map_one]
    exact h
  · intro h
    rw [← map_pow, h, map_one]

/-- One Galois automorphism restricted to `mu_n(A)`. -/
def rootsOfUnityActionMulAut
    (pair : SourceMLFGaloisTMPair G) (n : ℕ+)
    (g : G) : MulAut (pair.arithmeticMonoid.RootsOfUnityGroup n) where
  toFun unit :=
    ⟨pair.unitActionMulAut g unit.1,
      (pair.unitAction_mem_rootsOfUnity_iff n g unit.1).mpr unit.2⟩
  invFun unit :=
    ⟨pair.unitActionMulAut g⁻¹ unit.1,
      (pair.unitAction_mem_rootsOfUnity_iff n g⁻¹ unit.1).mpr unit.2⟩
  left_inv unit := by
    apply Subtype.ext
    apply Units.ext
    simp [unitActionMulAut]
  right_inv unit := by
    apply Subtype.ext
    apply Units.ext
    simp [unitActionMulAut]
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul (pair.unitActionMulAut g) first.1 second.1

/-- The Galois action on the literal finite group `mu_n(A)`. -/
def rootsOfUnityAction
    (pair : SourceMLFGaloisTMPair G) (n : ℕ+) :
    G →* MulAut (pair.arithmeticMonoid.RootsOfUnityGroup n) where
  toFun := pair.rootsOfUnityActionMulAut n
  map_one' := by
    apply MulEquiv.ext
    intro unit
    apply Subtype.ext
    apply Units.ext
    simp [rootsOfUnityActionMulAut, unitActionMulAut]
  map_mul' first second := by
    apply MulEquiv.ext
    intro unit
    apply Subtype.ext
    apply Units.ext
    simp [rootsOfUnityActionMulAut, unitActionMulAut]

/-- The bad-place monoid `O^perp(A)` is stable under the ambient Galois action. -/
theorem badPerpMonoid_stable
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier)
    (characteristic_stable : ∀ g value,
      value ∈ characteristic → pair.action g value ∈ characteristic)
    (g : G) (value : pair.arithmeticMonoid.carrier)
    (hvalue : value ∈ pair.badPerpMonoid l characteristic) :
    pair.action g value ∈ pair.badPerpMonoid l characteristic := by
  rcases Submonoid.mem_sup.mp hvalue with
    ⟨rootValue, hrootValue,
      characteristicValue, hcharacteristicValue, hfactor⟩
  refine Submonoid.mem_sup.mpr
    ⟨pair.action g rootValue, ?_,
      pair.action g characteristicValue,
      characteristic_stable g characteristicValue hcharacteristicValue, ?_⟩
  · rcases hrootValue with ⟨rootUnit, hrootUnit, hrootUnitValue⟩
    let mappedRoot : pair.arithmeticMonoid.RootsOfUnityGroup (twoEll l) :=
      pair.rootsOfUnityActionMulAut (twoEll l) g ⟨rootUnit, hrootUnit⟩
    refine
      (pair.arithmeticMonoid.rootsOfUnitySubgroup (twoEll l)).mem_ofUnits
        mappedRoot.2 ?_
    change (pair.unitActionMulAut g rootUnit :
      pair.arithmeticMonoid.carrier) = pair.action g rootValue
    rw [← hrootUnitValue]
    rfl
  · rw [← map_mul, hfactor]

/-- The restricted Galois action on `O^perp(A)` at a bad finite place. -/
def badPerpAction
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier)
    (characteristic_stable : ∀ g value,
      value ∈ characteristic → pair.action g value ∈ characteristic) :
    G →* MulAut (pair.badPerpMonoid l characteristic) :=
  pair.stableSubmonoidAction _
    (pair.badPerpMonoid_stable l characteristic characteristic_stable)

/-- The action on `O^perp(A)` restricts to the constructed action on `mu_(2 ell)(A)`. -/
theorem badPerpAction_subgroupUnits
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier)
    (characteristic_stable : ∀ g value,
      value ∈ characteristic → pair.action g value ∈ characteristic)
    (g : G) (unit : pair.TwoEllRootsOfUnity l) :
    pair.badPerpAction l characteristic characteristic_stable g
        (SourceSplitKummerMonoid.subgroupUnits
          (pair.badPerpMonoid l characteristic)
          (pair.arithmeticMonoid.rootsOfUnitySubgroup (twoEll l))
          le_sup_left unit : pair.badPerpMonoid l characteristic) =
      (SourceSplitKummerMonoid.subgroupUnits
        (pair.badPerpMonoid l characteristic)
        (pair.arithmeticMonoid.rootsOfUnitySubgroup (twoEll l))
        le_sup_left
        (pair.rootsOfUnityAction (twoEll l) g unit) :
          pair.badPerpMonoid l characteristic) := by
  apply Subtype.ext
  rfl

/-- The natural Galois action descended to `O^square(A)` at a bad finite place. -/
noncomputable def badCharacteristicAction
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier)
    (characteristic_stable : ∀ g value,
      value ∈ characteristic → pair.action g value ∈ characteristic) :
    G →* MulAut (pair.badCharacteristicQuotient l characteristic) :=
  SourceSplitKummerMonoid.unitQuotientAction
    (pair.badPerpMonoid l characteristic)
    (pair.arithmeticMonoid.rootsOfUnitySubgroup (twoEll l))
    le_sup_left
    (pair.badPerpAction l characteristic characteristic_stable)
    (pair.rootsOfUnityAction (twoEll l))
    (pair.badPerpAction_subgroupUnits l characteristic characteristic_stable)

@[simp]
theorem badCharacteristicAction_mk
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier)
    (characteristic_stable : ∀ g value,
      value ∈ characteristic → pair.action g value ∈ characteristic)
    (g : G) (value : pair.badPerpMonoid l characteristic) :
    pair.badCharacteristicAction l characteristic characteristic_stable g value =
      (pair.badPerpAction l characteristic characteristic_stable g value :
        pair.badCharacteristicQuotient l characteristic) := by
  exact SourceSplitKummerMonoid.unitQuotientMulAut_mk
    _ _ _ _ _ _ value

/-- The componentwise natural Galois action on bad-place `O^(square times-mu)`. -/
noncomputable def badTimesMuAction
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier)
    (characteristic_stable : ∀ g value,
      value ∈ characteristic → pair.action g value ∈ characteristic) :
    G →* MulAut (pair.badTimesMuMonoid l characteristic) :=
  SourceSplitKummerMonoid.productAction
    (pair.badCharacteristicAction l characteristic characteristic_stable)
    pair.unitModuloTorsionAction

/-- The componentwise natural Galois action on good-place `O^(square times-mu)`. -/
noncomputable def goodTimesMuAction
    (pair : SourceMLFGaloisTMPair G)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier)
    (characteristic_stable : ∀ g value,
      value ∈ characteristic → pair.action g value ∈ characteristic) :
    G →* MulAut (pair.goodTimesMuMonoid characteristic) :=
  SourceSplitKummerMonoid.productAction
    (pair.stableSubmonoidAction characteristic characteristic_stable)
    pair.unitModuloTorsionAction

/-- The bad-place identification of units with `O^(times-mu)` is G-equivariant. -/
theorem badTimesMuUnitsEquiv_equivariant
    (pair : SourceMLFGaloisTMPair G) (l : PrimeGeFive)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier)
    (hinjective : Function.Injective
      (SourceSplitKummerMonoid.unitCharacteristicMultiplication
        characteristic))
    (characteristic_stable : ∀ g value,
      value ∈ characteristic → pair.action g value ∈ characteristic)
    (g : G) (unit : (pair.badTimesMuMonoid l characteristic)ˣ) :
    pair.badTimesMuUnitsEquiv l characteristic hinjective
        (Units.map
          (pair.badTimesMuAction l characteristic characteristic_stable g).toMonoidHom
          unit) =
      pair.unitModuloTorsionAction g
        (pair.badTimesMuUnitsEquiv l characteristic hinjective unit) := by
  rfl

/-- The good-place identification of units with `O^(times-mu)` is G-equivariant. -/
theorem goodTimesMuUnitsEquiv_equivariant
    (pair : SourceMLFGaloisTMPair G)
    (characteristic : Submonoid pair.arithmeticMonoid.carrier)
    (hinjective : Function.Injective
      (SourceSplitKummerMonoid.unitCharacteristicMultiplication
        characteristic))
    (characteristic_stable : ∀ g value,
      value ∈ characteristic → pair.action g value ∈ characteristic)
    (g : G) (unit : (pair.goodTimesMuMonoid characteristic)ˣ) :
    pair.goodTimesMuUnitsEquiv characteristic hinjective
        (Units.map
          (pair.goodTimesMuAction characteristic characteristic_stable g).toMonoidHom
          unit) =
      pair.unitModuloTorsionAction g
        (pair.goodTimesMuUnitsEquiv characteristic hinjective unit) := by
  rfl

end SourceMLFGaloisTMPair

end Iut
