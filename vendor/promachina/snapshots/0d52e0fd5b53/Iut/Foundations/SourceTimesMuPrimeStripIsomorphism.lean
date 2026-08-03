/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTimesMuPrimeStrip

/-!
# Isomorphisms of the `F^times-mu` prime strips

IUT II, Definition 4.9(vii), defines a morphism of prime strips to be a
place-indexed collection of isomorphisms of the complete constituent data.
This file starts with the finite-place constituent.  In particular, the maps
below preserve the Galois action, every open-subgroup invariant Kummer image,
the characteristic factor, and the model-Frobenioid reconstruction.  A bare
equivalence of the carrier categories is not sufficient.
-/

open CategoryTheory

namespace Iut

universe u

/-! ## Equivalences of MLF-Galois `TM` pairs -/

/-- Transport an open subgroup forward through a topological group isomorphism. -/
def sourceTimesMuPushOpenSubgroup
    {G H : TopologicalGroupCat.{u}}
    (equivalence : G ≃ₜ* H) (subgroup : OpenSubgroup G) :
    OpenSubgroup H :=
  OpenSubgroup.comap equivalence.symm.toMonoidHom
    equivalence.symm.continuous_toFun subgroup

/-- Transport an open subgroup backward through a topological group isomorphism. -/
def sourceTimesMuPullOpenSubgroup
    {G H : TopologicalGroupCat.{u}}
    (equivalence : G ≃ₜ* H) (subgroup : OpenSubgroup H) :
    OpenSubgroup G :=
  OpenSubgroup.comap equivalence.toMonoidHom
    equivalence.continuous_toFun subgroup

@[simp]
theorem sourceTimesMuPushOpenSubgroup_refl
    {G : TopologicalGroupCat.{u}} (subgroup : OpenSubgroup G) :
    sourceTimesMuPushOpenSubgroup (ContinuousMulEquiv.refl G) subgroup =
      subgroup := by
  apply OpenSubgroup.ext
  intro value
  rfl

theorem sourceTimesMuPushOpenSubgroup_trans
    {G H L : TopologicalGroupCat.{u}}
    (first : G ≃ₜ* H) (second : H ≃ₜ* L)
    (subgroup : OpenSubgroup G) :
    sourceTimesMuPushOpenSubgroup (first.trans second) subgroup =
      sourceTimesMuPushOpenSubgroup second
        (sourceTimesMuPushOpenSubgroup first subgroup) := by
  apply OpenSubgroup.ext
  intro value
  rfl

theorem sourceTimesMuPullOpenSubgroup_trans
    {G H L : TopologicalGroupCat.{u}}
    (first : G ≃ₜ* H) (second : H ≃ₜ* L)
    (subgroup : OpenSubgroup L) :
    sourceTimesMuPullOpenSubgroup (first.trans second) subgroup =
      sourceTimesMuPullOpenSubgroup first
        (sourceTimesMuPullOpenSubgroup second subgroup) := by
  apply OpenSubgroup.ext
  intro value
  rfl

@[simp]
theorem sourceTimesMuPush_pullOpenSubgroup
    {G H : TopologicalGroupCat.{u}}
    (equivalence : G ≃ₜ* H) (subgroup : OpenSubgroup H) :
    sourceTimesMuPushOpenSubgroup equivalence
        (sourceTimesMuPullOpenSubgroup equivalence subgroup) = subgroup := by
  apply OpenSubgroup.ext
  intro value
  change equivalence (equivalence.symm value) ∈ subgroup ↔ value ∈ subgroup
  rw [equivalence.apply_symm_apply]

@[simp]
theorem sourceTimesMuPull_pushOpenSubgroup
    {G H : TopologicalGroupCat.{u}}
    (equivalence : G ≃ₜ* H) (subgroup : OpenSubgroup G) :
    sourceTimesMuPullOpenSubgroup equivalence
        (sourceTimesMuPushOpenSubgroup equivalence subgroup) = subgroup := by
  apply OpenSubgroup.ext
  intro value
  change equivalence.symm (equivalence value) ∈ subgroup ↔ value ∈ subgroup
  rw [equivalence.symm_apply_apply]

/--
An equivariant isomorphism of the complete MLF-Galois `TM` pair data.

Both directions of the invariant-image condition are retained.  This is what
allows an internal `times-mu` Kummer comparison to be transported through an
isomorphism without losing any of the open-subgroup data that defines `Ism`.
-/
structure SourceMLFGaloisTMPairEquivalence
    {G H : TopologicalGroupCat.{u}}
    (source : SourceMLFGaloisTMPair G)
    (target : SourceMLFGaloisTMPair H) where
  group : G ≃ₜ* H
  arithmeticMonoid :
    source.arithmeticMonoid.carrier ≃*
      target.arithmeticMonoid.carrier
  arithmeticMonoid_equivariant :
    ∀ g value,
      arithmeticMonoid (source.action g value) =
        target.action (group g) (arithmeticMonoid value)
  unitModuloTorsion :
    source.UnitModuloTorsion ≃* target.UnitModuloTorsion
  unitModuloTorsion_mk :
    ∀ unit : source.arithmeticMonoid.carrierˣ,
      unitModuloTorsion (QuotientGroup.mk unit) =
        QuotientGroup.mk
          (Units.mapEquiv arithmeticMonoid unit)
  unitModuloTorsion_equivariant :
    ∀ g value,
      unitModuloTorsion (source.unitModuloTorsionAction g value) =
        target.unitModuloTorsionAction (group g)
          (unitModuloTorsion value)
  invariantImage_forward :
    ∀ subgroup,
      unitModuloTorsion ''
          (source.invariantUnitImage subgroup :
            Set source.UnitModuloTorsion) =
        (target.invariantUnitImage
          (sourceTimesMuPushOpenSubgroup group subgroup) :
            Set target.UnitModuloTorsion)
  invariantImage_backward :
    ∀ subgroup,
      unitModuloTorsion.symm ''
          (target.invariantUnitImage subgroup :
            Set target.UnitModuloTorsion) =
        (source.invariantUnitImage
          (sourceTimesMuPullOpenSubgroup group subgroup) :
            Set source.UnitModuloTorsion)

namespace SourceMLFGaloisTMPairEquivalence

variable
    {G H L : TopologicalGroupCat.{u}}
    {source : SourceMLFGaloisTMPair G}
    {middle : SourceMLFGaloisTMPair H}
    {target : SourceMLFGaloisTMPair L}

/-- Identity equivalence of a complete MLF-Galois `TM` pair. -/
noncomputable def refl (source : SourceMLFGaloisTMPair G) :
    SourceMLFGaloisTMPairEquivalence source source where
  group := ContinuousMulEquiv.refl G
  arithmeticMonoid := MulEquiv.refl _
  arithmeticMonoid_equivariant _ _ := rfl
  unitModuloTorsion := MulEquiv.refl _
  unitModuloTorsion_mk _ := rfl
  unitModuloTorsion_equivariant _ _ := rfl
  invariantImage_forward subgroup := by
    rw [sourceTimesMuPushOpenSubgroup_refl]
    exact Set.image_id _
  invariantImage_backward subgroup := by
    change id ''
        (source.invariantUnitImage subgroup :
          Set source.UnitModuloTorsion) = _
    rw [Set.image_id]
    rfl

/-- Composition of equivariant MLF-Galois `TM`-pair equivalences. -/
noncomputable def trans
    (first : SourceMLFGaloisTMPairEquivalence source middle)
    (second : SourceMLFGaloisTMPairEquivalence middle target) :
    SourceMLFGaloisTMPairEquivalence source target where
  group := first.group.trans second.group
  arithmeticMonoid :=
    first.arithmeticMonoid.trans second.arithmeticMonoid
  arithmeticMonoid_equivariant g value := by
    change
      second.arithmeticMonoid
          (first.arithmeticMonoid (source.action g value)) =
        target.action (second.group (first.group g))
          (second.arithmeticMonoid
            (first.arithmeticMonoid value))
    rw [first.arithmeticMonoid_equivariant]
    exact second.arithmeticMonoid_equivariant (first.group g)
      (first.arithmeticMonoid value)
  unitModuloTorsion :=
    first.unitModuloTorsion.trans second.unitModuloTorsion
  unitModuloTorsion_mk unit := by
    change
      second.unitModuloTorsion
          (first.unitModuloTorsion (QuotientGroup.mk unit)) =
        QuotientGroup.mk
          (Units.mapEquiv
            (first.arithmeticMonoid.trans second.arithmeticMonoid) unit)
    rw [first.unitModuloTorsion_mk]
    rw [second.unitModuloTorsion_mk]
    rfl
  unitModuloTorsion_equivariant g value := by
    change
      second.unitModuloTorsion
          (first.unitModuloTorsion
            (source.unitModuloTorsionAction g value)) =
        target.unitModuloTorsionAction
          (second.group (first.group g))
          (second.unitModuloTorsion
            (first.unitModuloTorsion value))
    rw [first.unitModuloTorsion_equivariant]
    exact second.unitModuloTorsion_equivariant (first.group g)
      (first.unitModuloTorsion value)
  invariantImage_forward subgroup := by
    change
      (fun value => second.unitModuloTorsion
        (first.unitModuloTorsion value)) ''
          (source.invariantUnitImage subgroup :
            Set source.UnitModuloTorsion) = _
    rw [← Set.image_image]
    rw [first.invariantImage_forward]
    rw [second.invariantImage_forward]
    rw [sourceTimesMuPushOpenSubgroup_trans]
  invariantImage_backward subgroup := by
    change
      (fun value => first.unitModuloTorsion.symm
        (second.unitModuloTorsion.symm value)) ''
          (target.invariantUnitImage subgroup :
            Set target.UnitModuloTorsion) = _
    rw [← Set.image_image]
    rw [second.invariantImage_backward]
    rw [first.invariantImage_backward]
    rw [sourceTimesMuPullOpenSubgroup_trans]

/-- Equivariance of the inverse unit-quotient map. -/
theorem unitModuloTorsion_symm_equivariant
    (equivalence : SourceMLFGaloisTMPairEquivalence source middle)
    (g : H) (value : middle.UnitModuloTorsion) :
    equivalence.unitModuloTorsion.symm
        (middle.unitModuloTorsionAction g value) =
      source.unitModuloTorsionAction (equivalence.group.symm g)
        (equivalence.unitModuloTorsion.symm value) := by
  apply equivalence.unitModuloTorsion.injective
  rw [equivalence.unitModuloTorsion.apply_symm_apply]
  rw [equivalence.unitModuloTorsion_equivariant]
  rw [equivalence.group.apply_symm_apply]
  rw [equivalence.unitModuloTorsion.apply_symm_apply]

end SourceMLFGaloisTMPairEquivalence

namespace SourceMLFGaloisTMPair.TimesMuKummerIsomorphism

variable
    {G H : TopologicalGroupCat.{u}}
    {sourceGroup sourceCover : SourceMLFGaloisTMPair G}
    {targetGroup targetCover : SourceMLFGaloisTMPair H}

/--
Transport a complete `times-mu` Kummer comparison through equivariant
isomorphisms of its group-theoretic and covering pairs.
-/
noncomputable def transport
    (groupEquivalence :
      SourceMLFGaloisTMPairEquivalence sourceGroup targetGroup)
    (coverEquivalence :
      SourceMLFGaloisTMPairEquivalence sourceCover targetCover)
    (sameGroup : groupEquivalence.group = coverEquivalence.group)
    (comparison : TimesMuKummerIsomorphism sourceGroup sourceCover) :
    TimesMuKummerIsomorphism targetGroup targetCover where
  equiv :=
    groupEquivalence.unitModuloTorsion.symm.trans
      (comparison.equiv.trans
        coverEquivalence.unitModuloTorsion)
  equivariant g value := by
    change
      coverEquivalence.unitModuloTorsion
          (comparison.equiv
            (groupEquivalence.unitModuloTorsion.symm
              (targetGroup.unitModuloTorsionAction g value))) =
        targetCover.unitModuloTorsionAction g
          (coverEquivalence.unitModuloTorsion
            (comparison.equiv
              (groupEquivalence.unitModuloTorsion.symm value)))
    rw [groupEquivalence.unitModuloTorsion_symm_equivariant]
    rw [comparison.equivariant]
    rw [coverEquivalence.unitModuloTorsion_equivariant]
    rw [← sameGroup]
    rw [groupEquivalence.group.apply_symm_apply]
  invariantImage subgroup := by
    ext value
    constructor
    · rintro ⟨sourceValue, hsourceValue, rfl⟩
      have hgroupImage :
          groupEquivalence.unitModuloTorsion.symm sourceValue ∈
            groupEquivalence.unitModuloTorsion.symm ''
              (targetGroup.invariantUnitImage subgroup :
                Set targetGroup.UnitModuloTorsion) :=
        ⟨sourceValue, hsourceValue, rfl⟩
      rw [groupEquivalence.invariantImage_backward] at hgroupImage
      have hkummerImage :
          comparison.equiv
              (groupEquivalence.unitModuloTorsion.symm sourceValue) ∈
            comparison.equiv ''
              (sourceGroup.invariantUnitImage
                (sourceTimesMuPullOpenSubgroup
                  groupEquivalence.group subgroup) :
                Set sourceGroup.UnitModuloTorsion) :=
        ⟨_, hgroupImage, rfl⟩
      rw [comparison.invariantImage] at hkummerImage
      have hcoverImage :
          coverEquivalence.unitModuloTorsion
              (comparison.equiv
                (groupEquivalence.unitModuloTorsion.symm sourceValue)) ∈
            coverEquivalence.unitModuloTorsion ''
              (sourceCover.invariantUnitImage
                (sourceTimesMuPullOpenSubgroup
                  groupEquivalence.group subgroup) :
                Set sourceCover.UnitModuloTorsion) :=
        ⟨_, hkummerImage, rfl⟩
      rw [coverEquivalence.invariantImage_forward] at hcoverImage
      rw [← sameGroup,
        sourceTimesMuPush_pullOpenSubgroup] at hcoverImage
      exact hcoverImage
    · intro hvalue
      have hcoverImage :
          value ∈ coverEquivalence.unitModuloTorsion ''
            (sourceCover.invariantUnitImage
              (sourceTimesMuPullOpenSubgroup
                groupEquivalence.group subgroup) :
              Set sourceCover.UnitModuloTorsion) := by
        rw [coverEquivalence.invariantImage_forward]
        rwa [← sameGroup,
          sourceTimesMuPush_pullOpenSubgroup]
      rcases hcoverImage with ⟨coverValue, hcoverValue, rfl⟩
      have hkummerImage :
          coverValue ∈ comparison.equiv ''
            (sourceGroup.invariantUnitImage
              (sourceTimesMuPullOpenSubgroup
                groupEquivalence.group subgroup) :
              Set sourceGroup.UnitModuloTorsion) := by
        rw [comparison.invariantImage]
        exact hcoverValue
      rcases hkummerImage with ⟨groupValue, hgroupValue, rfl⟩
      have hgroupImage :
          groupValue ∈ groupEquivalence.unitModuloTorsion.symm ''
            (targetGroup.invariantUnitImage subgroup :
              Set targetGroup.UnitModuloTorsion) := by
        rw [groupEquivalence.invariantImage_backward]
        exact hgroupValue
      rcases hgroupImage with ⟨targetValue, htargetValue, htargetValueEq⟩
      refine ⟨targetValue, htargetValue, ?_⟩
      change
        coverEquivalence.unitModuloTorsion
            (comparison.equiv
              (groupEquivalence.unitModuloTorsion.symm targetValue)) =
          coverEquivalence.unitModuloTorsion
            (comparison.equiv groupValue)
      rw [htargetValueEq]

end SourceMLFGaloisTMPair.TimesMuKummerIsomorphism

/--
The `Ism`-orbit transported through two pair equivalences.  A representative
is selected only to define the quotient map; the theorem below proves that
the result is independent of this selection.
-/
noncomputable def sourceTimesMuTransportKummerOrbit
    {G H : TopologicalGroupCat.{u}}
    {sourceGroup sourceCover : SourceMLFGaloisTMPair G}
    {targetGroup targetCover : SourceMLFGaloisTMPair H}
    (groupEquivalence :
      SourceMLFGaloisTMPairEquivalence sourceGroup targetGroup)
    (coverEquivalence :
      SourceMLFGaloisTMPairEquivalence sourceCover targetCover)
    (sameGroup : groupEquivalence.group = coverEquivalence.group)
    (orbit :
      SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.TimesMuKummerOrbit
        sourceGroup sourceCover) :
    SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.TimesMuKummerOrbit
      targetGroup targetCover :=
  SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.orbitOf
    (SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.transport
      groupEquivalence coverEquivalence sameGroup
      (Classical.choose (Quotient.exists_rep orbit)))

/-- Every transported Kummer orbit is the unique target `Ism`-orbit. -/
theorem sourceTimesMuTransportKummerOrbit_eq
    {G H : TopologicalGroupCat.{u}}
    {sourceGroup sourceCover : SourceMLFGaloisTMPair G}
    {targetGroup targetCover : SourceMLFGaloisTMPair H}
    (groupEquivalence :
      SourceMLFGaloisTMPairEquivalence sourceGroup targetGroup)
    (coverEquivalence :
      SourceMLFGaloisTMPairEquivalence sourceCover targetCover)
    (sameGroup : groupEquivalence.group = coverEquivalence.group)
    (sourceOrbit :
      SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.TimesMuKummerOrbit
        sourceGroup sourceCover)
    (targetOrbit :
      SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.TimesMuKummerOrbit
        targetGroup targetCover) :
    sourceTimesMuTransportKummerOrbit groupEquivalence coverEquivalence
        sameGroup sourceOrbit = targetOrbit := by
  obtain ⟨targetRepresentative, rfl⟩ := Quotient.exists_rep targetOrbit
  exact
    SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.orbitOf_eq
      (SourceMLFGaloisTMPair.TimesMuKummerIsomorphism.transport
        groupEquivalence coverEquivalence sameGroup
        (Classical.choose (Quotient.exists_rep sourceOrbit)))
      targetRepresentative

namespace SourceFiniteTimesMuKummerInput

/-- The characteristic generator embedded in the reconstructed product monoid. -/
noncomputable def characteristicGenerator
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (input : SourceFiniteTimesMuKummerInput ell underlying) :
    input.characteristic →* input.timesMuMonoid := by
  rcases input with
    ⟨kind, referenceObject, referenceObject_isotropic,
      selectedSplitting, galoisGroup, groupPair, coverPair,
      rationalMonoidIso, characteristic, characteristic_eq_splitting,
      characteristic_stable, unit_characteristic_injective,
      kummerStructure⟩
  cases kind with
  | bad =>
      let intoPerp :
          characteristic →*
            coverPair.badPerpMonoid ell characteristic :=
        characteristic.subtype.codRestrict
          (coverPair.badPerpMonoid ell characteristic)
          (fun value =>
            (show characteristic ≤
                coverPair.badPerpMonoid ell characteristic from
              le_sup_right) value.property)
      let intoQuotient :
          characteristic →*
            coverPair.badCharacteristicQuotient ell characteristic :=
        (SourceSplitKummerMonoid.unitCongruence
          (coverPair.badPerpMonoid ell characteristic)
          (coverPair.arithmeticMonoid.rootsOfUnitySubgroup
            (SourceMLFGaloisTMPair.twoEll ell))
          le_sup_left).mk'.comp intoPerp
      exact
        (MonoidHom.inl
          (coverPair.badCharacteristicQuotient ell characteristic)
          coverPair.UnitModuloTorsion).comp intoQuotient
  | good =>
      exact MonoidHom.inl characteristic coverPair.UnitModuloTorsion

/-- The unit-mod-torsion factor embedded in the reconstructed product monoid. -/
noncomputable def unitGenerator
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (input : SourceFiniteTimesMuKummerInput ell underlying) :
    input.coverPair.UnitModuloTorsion →* input.timesMuMonoid := by
  rcases input with
    ⟨kind, referenceObject, referenceObject_isotropic,
      selectedSplitting, galoisGroup, groupPair, coverPair,
      rationalMonoidIso, characteristic, characteristic_eq_splitting,
      characteristic_stable, unit_characteristic_injective,
      kummerStructure⟩
  cases kind with
  | bad =>
      exact MonoidHom.inr
        (coverPair.badCharacteristicQuotient ell characteristic)
        coverPair.UnitModuloTorsion
  | good =>
      exact MonoidHom.inr characteristic coverPair.UnitModuloTorsion

/-- Projection from the reconstructed product to its unit-mod-torsion factor. -/
noncomputable def unitProjection
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (input : SourceFiniteTimesMuKummerInput ell underlying) :
    input.timesMuMonoid →* input.coverPair.UnitModuloTorsion := by
  rcases input with
    ⟨kind, referenceObject, referenceObject_isotropic,
      selectedSplitting, galoisGroup, groupPair, coverPair,
      rationalMonoidIso, characteristic, characteristic_eq_splitting,
      characteristic_stable, unit_characteristic_injective,
      kummerStructure⟩
  cases kind with
  | bad =>
      exact MonoidHom.snd
        (coverPair.badCharacteristicQuotient ell characteristic)
        coverPair.UnitModuloTorsion
  | good =>
      exact MonoidHom.snd characteristic coverPair.UnitModuloTorsion

@[simp]
theorem unitProjection_unitGenerator
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (input : SourceFiniteTimesMuKummerInput ell underlying)
    (value : input.coverPair.UnitModuloTorsion) :
    input.unitProjection (input.unitGenerator value) = value := by
  rcases input with
    ⟨kind, referenceObject, referenceObject_isotropic,
      selectedSplitting, galoisGroup, groupPair, coverPair,
      rationalMonoidIso, characteristic, characteristic_eq_splitting,
      characteristic_stable, unit_characteristic_injective,
      kummerStructure⟩
  cases kind <;> rfl

@[simp]
theorem unitProjection_characteristicGenerator
    {ell : PrimeGeFive}
    {underlying : SplitFrobenioidPresentation.{u}}
    (input : SourceFiniteTimesMuKummerInput ell underlying)
    (value : input.characteristic) :
    input.unitProjection (input.characteristicGenerator value) = 1 := by
  rcases input with
    ⟨kind, referenceObject, referenceObject_isotropic,
      selectedSplitting, galoisGroup, groupPair, coverPair,
      rationalMonoidIso, characteristic, characteristic_eq_splitting,
      characteristic_stable, unit_characteristic_injective,
      kummerStructure⟩
  cases kind <;> rfl

end SourceFiniteTimesMuKummerInput

/-! ## Finite split-Kummer Frobenioid isomorphisms -/

/--
An isomorphism of the complete finite-place object constructed in IUT II,
Definition 4.9(iii)--(iv).

The two generator equations and the unit-projection equation identify the
map on the literal product `O^square x O^(times-mu)`.  The remaining fields
say that the reconstructed split Frobenioid, its base, reference object, and
rational-function monoid carry exactly that map.
-/
structure SourceFiniteTimesMuKummerFrobenioidEquivalence
    {ell : PrimeGeFive}
    {sourceUnderlying targetUnderlying :
      SplitFrobenioidPresentation.{u}}
    (source :
      SourceFiniteTimesMuKummerFrobenioid ell sourceUnderlying)
    (target :
      SourceFiniteTimesMuKummerFrobenioid ell targetUnderlying) where
  underlying :
    SplitFrobenioidEquivalence sourceUnderlying targetUnderlying
  kind_compatible : source.input.kind = target.input.kind
  groupPair :
    SourceMLFGaloisTMPairEquivalence
      source.input.groupPair target.input.groupPair
  coverPair :
    SourceMLFGaloisTMPairEquivalence
      source.input.coverPair target.input.coverPair
  galoisGroup_compatible : groupPair.group = coverPair.group
  characteristic_compatible :
    ∀ value,
      value ∈ source.input.characteristic ↔
        coverPair.arithmeticMonoid value ∈
          target.input.characteristic
  timesMuMonoid :
    source.input.timesMuMonoid ≃* target.input.timesMuMonoid
  timesMu_characteristicGenerator :
    ∀ value : source.input.characteristic,
      timesMuMonoid (source.input.characteristicGenerator value) =
        target.input.characteristicGenerator
          ⟨coverPair.arithmeticMonoid value.1,
            (characteristic_compatible value.1).mp value.2⟩
  timesMu_unitGenerator :
    ∀ value : source.input.coverPair.UnitModuloTorsion,
      timesMuMonoid (source.input.unitGenerator value) =
        target.input.unitGenerator
          (coverPair.unitModuloTorsion value)
  timesMu_unitProjection :
    ∀ value : source.input.timesMuMonoid,
      target.input.unitProjection (timesMuMonoid value) =
        coverPair.unitModuloTorsion
          (source.input.unitProjection value)
  reconstructed :
    SplitFrobenioidEquivalence
      source.reconstructed target.reconstructed
  base :
    CategoryTheory.Equivalence
      source.reconstructed.frobenioid.baseCategory
      target.reconstructed.frobenioid.baseCategory
  base_compatible :
    source.reconstructed.frobenioid.preFrobenioid.base ⋙ base.functor =
      reconstructed.carrier.functor ⋙
        target.reconstructed.frobenioid.preFrobenioid.base
  referenceIso :
    reconstructed.carrier.functor.obj source.referenceObject ≅
      target.referenceObject
  referenceRationalMonoid :
    source.reconstructed.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
        source.referenceObject ≃*
      target.reconstructed.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
        target.referenceObject
  referenceRationalMonoid_hom :
    ∀ value,
      (referenceRationalMonoid value).hom =
        referenceIso.inv ≫
          reconstructed.carrier.functor.map value.hom ≫
            referenceIso.hom
  rationalTimesMu_compatible :
    ∀ value,
      target.rationalMonoidIso (referenceRationalMonoid value) =
        timesMuMonoid (source.rationalMonoidIso value)

namespace SourceFiniteTimesMuKummerFrobenioidEquivalence

variable
    {ell : PrimeGeFive}
    {sourceUnderlying middleUnderlying targetUnderlying :
      SplitFrobenioidPresentation.{u}}
    {source :
      SourceFiniteTimesMuKummerFrobenioid ell sourceUnderlying}
    {middle :
      SourceFiniteTimesMuKummerFrobenioid ell middleUnderlying}
    {target :
      SourceFiniteTimesMuKummerFrobenioid ell targetUnderlying}

/-- Identity isomorphism of a finite split-Kummer Frobenioid. -/
noncomputable def refl
    (source : SourceFiniteTimesMuKummerFrobenioid ell sourceUnderlying) :
    SourceFiniteTimesMuKummerFrobenioidEquivalence source source where
  underlying := SplitFrobenioidEquivalence.refl _
  kind_compatible := rfl
  groupPair := SourceMLFGaloisTMPairEquivalence.refl _
  coverPair := SourceMLFGaloisTMPairEquivalence.refl _
  galoisGroup_compatible := rfl
  characteristic_compatible _ := Iff.rfl
  timesMuMonoid := MulEquiv.refl _
  timesMu_characteristicGenerator _ := rfl
  timesMu_unitGenerator _ := rfl
  timesMu_unitProjection _ := rfl
  reconstructed := SplitFrobenioidEquivalence.refl _
  base := CategoryTheory.Equivalence.refl
  base_compatible :=
    (Functor.comp_id
      source.reconstructed.frobenioid.preFrobenioid.base).trans
      (Functor.id_comp
        source.reconstructed.frobenioid.preFrobenioid.base).symm
  referenceIso := Iso.refl source.referenceObject
  referenceRationalMonoid := MulEquiv.refl _
  referenceRationalMonoid_hom value := by
    change value.hom =
      𝟙 source.referenceObject ≫ value.hom ≫ 𝟙 source.referenceObject
    rw [Category.id_comp]
    exact (Category.comp_id value.hom).symm
  rationalTimesMu_compatible _ := rfl

/-- Composition of complete finite split-Kummer Frobenioid isomorphisms. -/
noncomputable def trans
    (first :
      SourceFiniteTimesMuKummerFrobenioidEquivalence source middle)
    (second :
      SourceFiniteTimesMuKummerFrobenioidEquivalence middle target) :
    SourceFiniteTimesMuKummerFrobenioidEquivalence source target where
  underlying := first.underlying.trans second.underlying
  kind_compatible := first.kind_compatible.trans second.kind_compatible
  groupPair := first.groupPair.trans second.groupPair
  coverPair := first.coverPair.trans second.coverPair
  galoisGroup_compatible := by
    change
      first.groupPair.group.trans second.groupPair.group =
        first.coverPair.group.trans second.coverPair.group
    rw [first.galoisGroup_compatible,
      second.galoisGroup_compatible]
  characteristic_compatible value := by
    rw [first.characteristic_compatible]
    exact second.characteristic_compatible
      (first.coverPair.arithmeticMonoid value)
  timesMuMonoid := first.timesMuMonoid.trans second.timesMuMonoid
  timesMu_characteristicGenerator value := by
    change
      second.timesMuMonoid
          (first.timesMuMonoid
            (source.input.characteristicGenerator value)) = _
    rw [first.timesMu_characteristicGenerator]
    rw [second.timesMu_characteristicGenerator]
    rfl
  timesMu_unitGenerator value := by
    change
      second.timesMuMonoid
          (first.timesMuMonoid
            (source.input.unitGenerator value)) = _
    rw [first.timesMu_unitGenerator]
    rw [second.timesMu_unitGenerator]
    rfl
  timesMu_unitProjection value := by
    change
      target.input.unitProjection
          (second.timesMuMonoid (first.timesMuMonoid value)) = _
    rw [second.timesMu_unitProjection]
    rw [first.timesMu_unitProjection]
    rfl
  reconstructed := first.reconstructed.trans second.reconstructed
  base := first.base.trans second.base
  base_compatible := by
    change
      source.reconstructed.frobenioid.preFrobenioid.base ⋙
          (first.base.functor ⋙ second.base.functor) =
        (first.reconstructed.carrier.functor ⋙
            second.reconstructed.carrier.functor) ⋙
          target.reconstructed.frobenioid.preFrobenioid.base
    rw [← Functor.assoc]
    rw [first.base_compatible]
    rw [Functor.assoc]
    rw [second.base_compatible]
    rw [← Functor.assoc]
  referenceIso :=
    second.reconstructed.carrier.functor.mapIso first.referenceIso ≪≫
      second.referenceIso
  referenceRationalMonoid :=
    first.referenceRationalMonoid.trans
      second.referenceRationalMonoid
  referenceRationalMonoid_hom value := by
    change
      (second.referenceRationalMonoid
        (first.referenceRationalMonoid value)).hom =
        (second.reconstructed.carrier.functor.mapIso
              first.referenceIso ≪≫
            second.referenceIso).inv ≫
          second.reconstructed.carrier.functor.map
              (first.reconstructed.carrier.functor.map value.hom) ≫
            (second.reconstructed.carrier.functor.mapIso
                first.referenceIso ≪≫
              second.referenceIso).hom
    rw [second.referenceRationalMonoid_hom]
    rw [first.referenceRationalMonoid_hom]
    simp only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
  rationalTimesMu_compatible value := by
    change
      target.rationalMonoidIso
          (second.referenceRationalMonoid
            (first.referenceRationalMonoid value)) =
        second.timesMuMonoid
          (first.timesMuMonoid
            (source.rationalMonoidIso value))
    rw [second.rationalTimesMu_compatible]
    rw [first.rationalTimesMu_compatible]

/-- The finite isomorphism carries the literal source Kummer orbit to the target orbit. -/
theorem kummerStructure_compatible
    (equivalence :
      SourceFiniteTimesMuKummerFrobenioidEquivalence source target) :
    sourceTimesMuTransportKummerOrbit
        equivalence.groupPair equivalence.coverPair
        equivalence.galoisGroup_compatible
        source.input.kummerStructure =
      target.input.kummerStructure :=
  sourceTimesMuTransportKummerOrbit_eq
    equivalence.groupPair equivalence.coverPair
    equivalence.galoisGroup_compatible
    source.input.kummerStructure target.input.kummerStructure

end SourceFiniteTimesMuKummerFrobenioidEquivalence

/-! ## Archimedean torsion-quotient system isomorphisms -/

/--
A structure-preserving isomorphism between two reconstructed archimedean
stages.  Besides the split-Frobenioid equivalence, this retains the base,
divisor monoids, Frobenius degrees, and FSM morphisms.
-/
structure SourceArchimedeanTimesMuStageEquivalence
    {sourceUnderlying targetUnderlying :
      ArchimedeanSplitFrobenioidPresentation.{u}}
    {sourceQuotients :
      SourceArchimedeanTimesMuQuotientSystem sourceUnderlying}
    {targetQuotients :
      SourceArchimedeanTimesMuQuotientSystem targetUnderlying}
    {N : ℕ+}
    (source : SourceArchimedeanTimesMuStage sourceQuotients N)
    (target : SourceArchimedeanTimesMuStage targetQuotients N) where
  reconstructed :
    ArchimedeanSplitFrobenioidEquivalence
      source.reconstructed target.reconstructed
  base :
    CategoryTheory.Equivalence
      source.reconstructed.frobenioid.frobenioid.baseCategory
      target.reconstructed.frobenioid.frobenioid.baseCategory
  base_compatible :
    source.reconstructed.frobenioid.frobenioid.preFrobenioid.base ⋙
        base.functor =
      reconstructed.frobenioid.carrier.functor ⋙
        target.reconstructed.frobenioid.frobenioid.preFrobenioid.base
  divisor :
    ∀ X : SourceArchimedeanTimesMuStage.Carrier source,
      SourceArchimedeanTimesMuStage.DivisorAt source X ≃+
        SourceArchimedeanTimesMuStage.DivisorAt target
          (reconstructed.frobenioid.carrier.functor.obj X)
  divisor_compatible :
    ∀ {X Y : SourceArchimedeanTimesMuStage.Carrier source}
      (map : X ⟶ Y),
      divisor X
          (source.reconstructed.frobenioid.frobenioid.preFrobenioid.divisor
            map) =
        target.reconstructed.frobenioid.frobenioid.preFrobenioid.divisor
          (reconstructed.frobenioid.carrier.functor.map map)
  frobeniusDegree_compatible :
    ∀ {X Y : SourceArchimedeanTimesMuStage.Carrier source}
      (map : X ⟶ Y),
      target.reconstructed.frobenioid.frobenioid.preFrobenioid.frobeniusDegree
          (reconstructed.frobenioid.carrier.functor.map map) =
        source.reconstructed.frobenioid.frobenioid.preFrobenioid.frobeniusDegree
          map
  fsm_compatible :
    ∀ {X Y :
        source.reconstructed.frobenioid.frobenioid.baseCategory}
      (map : X ⟶ Y),
      source.reconstructed.frobenioid.frobenioid.isFSM map ->
        target.reconstructed.frobenioid.frobenioid.isFSM
          (base.functor.map map)
  referenceRationalMonoid :
    SourceArchimedeanTimesMuStage.ReferenceRationalMonoid source ≃*
      SourceArchimedeanTimesMuStage.ReferenceRationalMonoid target
  referenceRationalMonoid_hom :
    ∀ value,
      (referenceRationalMonoid value).hom =
        reconstructed.referenceIso.inv ≫
          reconstructed.frobenioid.carrier.functor.map value.hom ≫
            reconstructed.referenceIso.hom
  referenceTotal_compatible :
    ∀ value,
      target.reconstructed.rationalTotalIso
          (referenceRationalMonoid value) =
        reconstructed.topologicalSplitting.total.toHom
          (source.reconstructed.rationalTotalIso value)

namespace SourceArchimedeanTimesMuStageEquivalence

variable
    {sourceUnderlying middleUnderlying targetUnderlying :
      ArchimedeanSplitFrobenioidPresentation.{u}}
    {sourceQuotients :
      SourceArchimedeanTimesMuQuotientSystem sourceUnderlying}
    {middleQuotients :
      SourceArchimedeanTimesMuQuotientSystem middleUnderlying}
    {targetQuotients :
      SourceArchimedeanTimesMuQuotientSystem targetUnderlying}
    {N : ℕ+}
    {source : SourceArchimedeanTimesMuStage sourceQuotients N}
    {middle : SourceArchimedeanTimesMuStage middleQuotients N}
    {target : SourceArchimedeanTimesMuStage targetQuotients N}

/-- Identity isomorphism of a reconstructed archimedean stage. -/
def refl (source : SourceArchimedeanTimesMuStage sourceQuotients N) :
    SourceArchimedeanTimesMuStageEquivalence source source where
  reconstructed := ArchimedeanSplitFrobenioidEquivalence.refl _
  base := CategoryTheory.Equivalence.refl
  base_compatible :=
    (Functor.comp_id
      source.reconstructed.frobenioid.frobenioid.preFrobenioid.base).trans
      (Functor.id_comp
        source.reconstructed.frobenioid.frobenioid.preFrobenioid.base).symm
  divisor _ := AddEquiv.refl _
  divisor_compatible _ := rfl
  frobeniusDegree_compatible _ := rfl
  fsm_compatible _ hmap := hmap
  referenceRationalMonoid := MulEquiv.refl _
  referenceRationalMonoid_hom value := by
    change value.hom =
      𝟙 source.reconstructed.referenceObject ≫
        value.hom ≫ 𝟙 source.reconstructed.referenceObject
    rw [Category.id_comp]
    exact (Category.comp_id value.hom).symm
  referenceTotal_compatible _ := rfl

/-- Composition of reconstructed archimedean stage isomorphisms. -/
def trans
    (first : SourceArchimedeanTimesMuStageEquivalence source middle)
    (second : SourceArchimedeanTimesMuStageEquivalence middle target) :
    SourceArchimedeanTimesMuStageEquivalence source target where
  reconstructed := first.reconstructed.trans second.reconstructed
  base := first.base.trans second.base
  base_compatible := by
    change
      source.reconstructed.frobenioid.frobenioid.preFrobenioid.base ⋙
          (first.base.functor ⋙ second.base.functor) =
        (first.reconstructed.frobenioid.carrier.functor ⋙
            second.reconstructed.frobenioid.carrier.functor) ⋙
          target.reconstructed.frobenioid.frobenioid.preFrobenioid.base
    rw [← Functor.assoc]
    rw [first.base_compatible]
    rw [Functor.assoc]
    rw [second.base_compatible]
    rw [← Functor.assoc]
  divisor X :=
    (first.divisor X).trans
      (second.divisor
        (first.reconstructed.frobenioid.carrier.functor.obj X))
  divisor_compatible map := by
    change
      second.divisor
          (first.reconstructed.frobenioid.carrier.functor.obj _)
          (first.divisor _
            (source.reconstructed.frobenioid.frobenioid.preFrobenioid.divisor
              map)) = _
    rw [first.divisor_compatible]
    rw [second.divisor_compatible]
    rfl
  frobeniusDegree_compatible map := by
    change
      target.reconstructed.frobenioid.frobenioid.preFrobenioid.frobeniusDegree
          (second.reconstructed.frobenioid.carrier.functor.map
            (first.reconstructed.frobenioid.carrier.functor.map map)) = _
    rw [second.frobeniusDegree_compatible]
    rw [first.frobeniusDegree_compatible]
  fsm_compatible map hmap :=
    second.fsm_compatible _ (first.fsm_compatible map hmap)
  referenceRationalMonoid :=
    first.referenceRationalMonoid.trans
      second.referenceRationalMonoid
  referenceRationalMonoid_hom value := by
    change
      (second.referenceRationalMonoid
        (first.referenceRationalMonoid value)).hom =
        (second.reconstructed.frobenioid.carrier.functor.mapIso
              first.reconstructed.referenceIso ≪≫
            second.reconstructed.referenceIso).inv ≫
          second.reconstructed.frobenioid.carrier.functor.map
              (first.reconstructed.frobenioid.carrier.functor.map value.hom) ≫
            (second.reconstructed.frobenioid.carrier.functor.mapIso
                first.reconstructed.referenceIso ≪≫
              second.reconstructed.referenceIso).hom
    rw [second.referenceRationalMonoid_hom]
    rw [first.referenceRationalMonoid_hom]
    simp only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
  referenceTotal_compatible value := by
    change
      target.reconstructed.rationalTotalIso
          (second.referenceRationalMonoid
            (first.referenceRationalMonoid value)) =
        second.reconstructed.topologicalSplitting.total.toHom
          (first.reconstructed.topologicalSplitting.total.toHom
            (source.reconstructed.rationalTotalIso value))
    rw [second.referenceTotal_compatible]
    rw [first.referenceTotal_compatible]

end SourceArchimedeanTimesMuStageEquivalence

/--
An isomorphism of the complete archimedean inductive systems in Definition
4.9(v).  The level maps commute with the torsion quotients, the unique
orientation reversal, the reconstructed split topological monoids, and all
carrier, base, and reference-rational transition maps.
-/
structure SourceArchimedeanTimesMuSystemEquivalence
    {sourceUnderlying targetUnderlying :
      ArchimedeanSplitFrobenioidPresentation.{u}}
    (source : SourceArchimedeanTimesMuSystem sourceUnderlying)
    (target : SourceArchimedeanTimesMuSystem targetUnderlying) where
  underlying :
    ArchimedeanSplitFrobenioidEquivalence
      sourceUnderlying targetUnderlying
  unitQuotient :
    ∀ N, TopologicalMonoidIso
      (source.quotients.unitQuotient N)
      (target.quotients.unitQuotient N)
  quotientMap_compatible :
    ∀ N value,
      (unitQuotient N).toHom
          (source.quotients.quotientMap N value) =
        target.quotients.quotientMap N
          (underlying.topologicalSplitting.compactFactor.toHom value)
  orientationReversal_compatible :
    ∀ value,
      underlying.topologicalSplitting.compactFactor.toHom
          (source.quotients.orientationReversal.toHom value) =
        target.quotients.orientationReversal.toHom
          (underlying.topologicalSplitting.compactFactor.toHom value)
  quotientTransition_compatible :
    ∀ (N M : ℕ+) (hNM : N ∣ M) value,
      (unitQuotient M).toHom
          (source.quotients.transition N M hNM value) =
        target.quotients.transition N M hNM
          ((unitQuotient N).toHom value)
  stage :
    ∀ N, SourceArchimedeanTimesMuStageEquivalence
      (source.stage N) (target.stage N)
  quotientSplitting_compatible :
    ∀ N value,
      (target.stage N).quotientSplittingIso.total.toHom
          ((stage N).reconstructed.topologicalSplitting.total.toHom value) =
        ((unitQuotient N).toHom
            ((source.stage N).quotientSplittingIso.total.toHom value).1,
          underlying.topologicalSplitting.noncompactFactor.toHom
            ((source.stage N).quotientSplittingIso.total.toHom value).2)
  carrierTransition_natural :
    ∀ (N M : ℕ+) (hNM : N ∣ M),
      (stage N).reconstructed.frobenioid.carrier.functor ⋙
          target.carrierTransition N M hNM =
        source.carrierTransition N M hNM ⋙
          (stage M).reconstructed.frobenioid.carrier.functor
  baseTransition_natural :
    ∀ (N M : ℕ+) (hNM : N ∣ M),
      (stage N).base.functor ⋙ target.baseTransition N M hNM =
        source.baseTransition N M hNM ⋙ (stage M).base.functor
  rationalTransition_natural :
    ∀ (N M : ℕ+) (hNM : N ∣ M)
      (value :
        SourceArchimedeanTimesMuStage.ReferenceRationalMonoid
          (source.stage N)),
      (stage M).referenceRationalMonoid
          (source.rationalTransition N M hNM value) =
        target.rationalTransition N M hNM
          ((stage N).referenceRationalMonoid value)

namespace SourceArchimedeanTimesMuSystemEquivalence

variable
    {sourceUnderlying middleUnderlying targetUnderlying :
      ArchimedeanSplitFrobenioidPresentation.{u}}
    {source : SourceArchimedeanTimesMuSystem sourceUnderlying}
    {middle : SourceArchimedeanTimesMuSystem middleUnderlying}
    {target : SourceArchimedeanTimesMuSystem targetUnderlying}

/-- Identity isomorphism of an archimedean torsion-quotient system. -/
def refl (source : SourceArchimedeanTimesMuSystem sourceUnderlying) :
    SourceArchimedeanTimesMuSystemEquivalence source source where
  underlying := ArchimedeanSplitFrobenioidEquivalence.refl _
  unitQuotient N :=
    TopologicalMonoidIso.refl (source.quotients.unitQuotient N)
  quotientMap_compatible _ _ := rfl
  orientationReversal_compatible _ := rfl
  quotientTransition_compatible _ _ _ _ := rfl
  stage N := SourceArchimedeanTimesMuStageEquivalence.refl (source.stage N)
  quotientSplitting_compatible _ _ := rfl
  carrierTransition_natural N M hNM :=
    (Functor.id_comp (source.carrierTransition N M hNM)).trans
      (Functor.comp_id (source.carrierTransition N M hNM)).symm
  baseTransition_natural N M hNM :=
    (Functor.id_comp (source.baseTransition N M hNM)).trans
      (Functor.comp_id (source.baseTransition N M hNM)).symm
  rationalTransition_natural _ _ _ _ := rfl

/-- Composition of archimedean torsion-quotient system isomorphisms. -/
def trans
    (first : SourceArchimedeanTimesMuSystemEquivalence source middle)
    (second : SourceArchimedeanTimesMuSystemEquivalence middle target) :
    SourceArchimedeanTimesMuSystemEquivalence source target where
  underlying := first.underlying.trans second.underlying
  unitQuotient N :=
    (first.unitQuotient N).trans (second.unitQuotient N)
  quotientMap_compatible N value := by
    change
      (second.unitQuotient N).toHom
          ((first.unitQuotient N).toHom
            (source.quotients.quotientMap N value)) = _
    rw [first.quotientMap_compatible]
    rw [second.quotientMap_compatible]
    rfl
  orientationReversal_compatible value := by
    change
      second.underlying.topologicalSplitting.compactFactor.toHom
          (first.underlying.topologicalSplitting.compactFactor.toHom
            (source.quotients.orientationReversal.toHom value)) = _
    rw [first.orientationReversal_compatible]
    rw [second.orientationReversal_compatible]
    rfl
  quotientTransition_compatible N M hNM value := by
    change
      (second.unitQuotient M).toHom
          ((first.unitQuotient M).toHom
            (source.quotients.transition N M hNM value)) = _
    rw [first.quotientTransition_compatible]
    rw [second.quotientTransition_compatible]
    rfl
  stage N := (first.stage N).trans (second.stage N)
  quotientSplitting_compatible N value := by
    change
      (target.stage N).quotientSplittingIso.total.toHom
          ((second.stage N).reconstructed.topologicalSplitting.total.toHom
            ((first.stage N).reconstructed.topologicalSplitting.total.toHom
              value)) = _
    rw [second.quotientSplitting_compatible]
    rw [first.quotientSplitting_compatible]
    rfl
  carrierTransition_natural N M hNM := by
    change
      ((first.stage N).reconstructed.frobenioid.carrier.functor ⋙
          (second.stage N).reconstructed.frobenioid.carrier.functor) ⋙
            target.carrierTransition N M hNM =
        source.carrierTransition N M hNM ⋙
          ((first.stage M).reconstructed.frobenioid.carrier.functor ⋙
            (second.stage M).reconstructed.frobenioid.carrier.functor)
    rw [Functor.assoc]
    rw [second.carrierTransition_natural]
    rw [← Functor.assoc]
    rw [first.carrierTransition_natural]
    rw [Functor.assoc]
  baseTransition_natural N M hNM := by
    change
      ((first.stage N).base.functor ⋙ (second.stage N).base.functor) ⋙
          target.baseTransition N M hNM =
        source.baseTransition N M hNM ⋙
          ((first.stage M).base.functor ⋙ (second.stage M).base.functor)
    rw [Functor.assoc]
    rw [second.baseTransition_natural]
    rw [← Functor.assoc]
    rw [first.baseTransition_natural]
    rw [Functor.assoc]
  rationalTransition_natural N M hNM value := by
    change
      (second.stage M).referenceRationalMonoid
          ((first.stage M).referenceRationalMonoid
            (source.rationalTransition N M hNM value)) =
        target.rationalTransition N M hNM
          ((second.stage N).referenceRationalMonoid
            ((first.stage N).referenceRationalMonoid value))
    rw [first.rationalTransition_natural]
    rw [second.rationalTransition_natural]

end SourceArchimedeanTimesMuSystemEquivalence

namespace SourceArchimedeanTimesMuStageEquivalence

/-- A stage isomorphism restricts to the divisor-zero isometry coarsification. -/
def isometryFunctor
    {sourceUnderlying targetUnderlying :
      ArchimedeanSplitFrobenioidPresentation.{u}}
    {sourceQuotients :
      SourceArchimedeanTimesMuQuotientSystem sourceUnderlying}
    {targetQuotients :
      SourceArchimedeanTimesMuQuotientSystem targetUnderlying}
    {N : ℕ+}
    {source : SourceArchimedeanTimesMuStage sourceQuotients N}
    {target : SourceArchimedeanTimesMuStage targetQuotients N}
    (equivalence :
      SourceArchimedeanTimesMuStageEquivalence source target) :
    source.reconstructed.frobenioid.frobenioid.preFrobenioid.IsometryCategory ⥤
      target.reconstructed.frobenioid.frobenioid.preFrobenioid.IsometryCategory where
  obj object :=
    ⟨equivalence.reconstructed.frobenioid.carrier.functor.obj object.obj⟩
  map {first second} map :=
    { hom :=
        equivalence.reconstructed.frobenioid.carrier.functor.map map.hom
      property := by
        change
          target.reconstructed.frobenioid.frobenioid.preFrobenioid.divisor
              (equivalence.reconstructed.frobenioid.carrier.functor.map
                map.hom) = 0
        rw [← equivalence.divisor_compatible map.hom]
        rw [map.property]
        exact map_zero (equivalence.divisor first.obj) }
  map_id object := by
    apply WideSubcategory.hom_ext
    exact equivalence.reconstructed.frobenioid.carrier.functor.map_id object.obj
  map_comp first second := by
    apply WideSubcategory.hom_ext
    exact equivalence.reconstructed.frobenioid.carrier.functor.map_comp
      first.hom second.hom

end SourceArchimedeanTimesMuStageEquivalence

namespace SourceArchimedeanTimesMuSystem

/-- The generic transition on the divisor-zero coarsifications of a system. -/
def isometryTransition
    {underlying : ArchimedeanSplitFrobenioidPresentation.{u}}
    (system : SourceArchimedeanTimesMuSystem underlying)
    (N M : ℕ+) (hNM : N ∣ M) :
    (system.stage N).reconstructed.frobenioid.frobenioid.preFrobenioid.IsometryCategory ⥤
      (system.stage M).reconstructed.frobenioid.frobenioid.preFrobenioid.IsometryCategory where
  obj object := ⟨(system.carrierTransition N M hNM).obj object.obj⟩
  map {first second} map :=
    { hom := (system.carrierTransition N M hNM).map map.hom
      property := by
        change
          (system.stage M).reconstructed.frobenioid.frobenioid.preFrobenioid.divisor
              ((system.carrierTransition N M hNM).map map.hom) = 0
        rw [← system.divisor_compatible N M hNM map.hom]
        rw [map.property]
        exact map_zero _ }
  map_id object := by
    apply WideSubcategory.hom_ext
    exact (system.carrierTransition N M hNM).map_id object.obj
  map_comp first second := by
    apply WideSubcategory.hom_ext
    exact (system.carrierTransition N M hNM).map_comp first.hom second.hom

end SourceArchimedeanTimesMuSystem

namespace SourceArchimedeanTimesMuSystemEquivalence

/-- The levelwise carrier equivalences form a natural map of divisibility diagrams. -/
def carrierNaturalTransformation
    {sourceUnderlying targetUnderlying :
      ArchimedeanSplitFrobenioidPresentation.{u}}
    {source : SourceArchimedeanTimesMuSystem sourceUnderlying}
    {target : SourceArchimedeanTimesMuSystem targetUnderlying}
    (equivalence :
      SourceArchimedeanTimesMuSystemEquivalence source target) :
    source.carrierDiagram ⟶ target.carrierDiagram where
  app index :=
    (equivalence.stage index.value).reconstructed.frobenioid.carrier.functor.toCatHom
  naturality {first second} map := by
    apply Cat.Hom.ext
    exact (equivalence.carrierTransition_natural
      first.value second.value map.le).symm

/-- Every component of the carrier-diagram map is an equivalence of categories. -/
theorem carrierNaturalTransformation_app_isEquivalence
    {sourceUnderlying targetUnderlying :
      ArchimedeanSplitFrobenioidPresentation.{u}}
    {source : SourceArchimedeanTimesMuSystem sourceUnderlying}
    {target : SourceArchimedeanTimesMuSystem targetUnderlying}
    (equivalence :
      SourceArchimedeanTimesMuSystemEquivalence source target)
    (index : SourceArchimedeanKummerSystem.DivisibilityIndex) :
    (equivalence.carrierNaturalTransformation.app index).toFunctor.IsEquivalence := by
  change
    (equivalence.stage index.value).reconstructed.frobenioid.carrier.functor.IsEquivalence
  exact
    (equivalence.stage index.value).reconstructed.frobenioid.carrier.isEquivalence_functor

end SourceArchimedeanTimesMuSystemEquivalence

/-! ## Place-indexed and global maps -/

/-- A place-indexed isomorphism of all Definition 4.9(vi)--(vii) constituents. -/
structure SourceFTimesMuPrimeStripEquivalence
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta}
    {sourceUnderlying targetUnderlying :
      SourceFMonoAnalyticPrimeStrip models}
    (source : SourceFTimesMuPrimeStrip sourceUnderlying)
    (target : SourceFTimesMuPrimeStrip targetUnderlying) where
  finite :
    ∀ v, SourceFiniteTimesMuKummerFrobenioidEquivalence
      (source.finite v) (target.finite v)
  archimedean :
    ∀ v, SourceArchimedeanTimesMuSystemEquivalence
      (source.archimedean v) (target.archimedean v)

namespace SourceFTimesMuPrimeStripEquivalence

variable
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta}
    {sourceUnderlying middleUnderlying targetUnderlying :
      SourceFMonoAnalyticPrimeStrip models}
    {source : SourceFTimesMuPrimeStrip sourceUnderlying}
    {middle : SourceFTimesMuPrimeStrip middleUnderlying}
    {target : SourceFTimesMuPrimeStrip targetUnderlying}

/-- Identity place-indexed isomorphism. -/
noncomputable def refl
    (source : SourceFTimesMuPrimeStrip sourceUnderlying) :
    SourceFTimesMuPrimeStripEquivalence source source where
  finite v := SourceFiniteTimesMuKummerFrobenioidEquivalence.refl
    (source.finite v)
  archimedean v := SourceArchimedeanTimesMuSystemEquivalence.refl
    (source.archimedean v)

/-- Composition of place-indexed isomorphisms. -/
noncomputable def trans
    (first : SourceFTimesMuPrimeStripEquivalence source middle)
    (second : SourceFTimesMuPrimeStripEquivalence middle target) :
    SourceFTimesMuPrimeStripEquivalence source target where
  finite v := (first.finite v).trans (second.finite v)
  archimedean v := (first.archimedean v).trans (second.archimedean v)

end SourceFTimesMuPrimeStripEquivalence

/--
A structure-preserving equivalence of Frobenioid presentations, retaining the
base, divisor, Frobenius-degree, and FSM structures used by global
realification.
-/
structure SourceFrobenioidEquivalence
    (source target : FrobenioidPresentation.{u}) where
  carrier : CategoryTheory.Equivalence source.carrier target.carrier
  base : CategoryTheory.Equivalence source.baseCategory target.baseCategory
  base_compatible :
    source.preFrobenioid.base ⋙ base.functor =
      carrier.functor ⋙ target.preFrobenioid.base
  divisor :
    ∀ X : source.carrier,
      (source.preFrobenioid.divisorMonoid.obj
        (source.preFrobenioid.base.obj X)).carrier ≃+
      (target.preFrobenioid.divisorMonoid.obj
        (target.preFrobenioid.base.obj (carrier.functor.obj X))).carrier
  divisor_compatible :
    ∀ {X Y : source.carrier} (map : X ⟶ Y),
      divisor X (source.preFrobenioid.divisor map) =
        target.preFrobenioid.divisor (carrier.functor.map map)
  frobeniusDegree_compatible :
    ∀ {X Y : source.carrier} (map : X ⟶ Y),
      target.preFrobenioid.frobeniusDegree (carrier.functor.map map) =
        source.preFrobenioid.frobeniusDegree map
  fsm_compatible :
    ∀ {X Y : source.baseCategory} (map : X ⟶ Y),
      source.isFSM map -> target.isFSM (base.functor.map map)

namespace SourceFrobenioidEquivalence

variable {source middle target : FrobenioidPresentation.{u}}

/-- Identity structure-preserving Frobenioid equivalence. -/
def refl (source : FrobenioidPresentation.{u}) :
    SourceFrobenioidEquivalence source source where
  carrier := CategoryTheory.Equivalence.refl
  base := CategoryTheory.Equivalence.refl
  base_compatible :=
    (Functor.comp_id source.preFrobenioid.base).trans
      (Functor.id_comp source.preFrobenioid.base).symm
  divisor _ := AddEquiv.refl _
  divisor_compatible _ := rfl
  frobeniusDegree_compatible _ := rfl
  fsm_compatible _ hmap := hmap

/-- Composition of structure-preserving Frobenioid equivalences. -/
def trans
    (first : SourceFrobenioidEquivalence source middle)
    (second : SourceFrobenioidEquivalence middle target) :
    SourceFrobenioidEquivalence source target where
  carrier := first.carrier.trans second.carrier
  base := first.base.trans second.base
  base_compatible := by
    change
      source.preFrobenioid.base ⋙
          (first.base.functor ⋙ second.base.functor) =
        (first.carrier.functor ⋙ second.carrier.functor) ⋙
          target.preFrobenioid.base
    rw [← Functor.assoc]
    rw [first.base_compatible]
    rw [Functor.assoc]
    rw [second.base_compatible]
    rw [← Functor.assoc]
  divisor X :=
    (first.divisor X).trans (second.divisor (first.carrier.functor.obj X))
  divisor_compatible map := by
    change
      second.divisor (first.carrier.functor.obj _)
          (first.divisor _ (source.preFrobenioid.divisor map)) = _
    rw [first.divisor_compatible]
    rw [second.divisor_compatible]
    rfl
  frobeniusDegree_compatible map := by
    change
      target.preFrobenioid.frobeniusDegree
          (second.carrier.functor.map (first.carrier.functor.map map)) = _
    rw [second.frobeniusDegree_compatible]
    rw [first.frobeniusDegree_compatible]
  fsm_compatible map hmap :=
    second.fsm_compatible _ (first.fsm_compatible map hmap)

end SourceFrobenioidEquivalence

/--
An isomorphism of globally realified `F^times-mu` prime strips from
Definition 4.9(viii).  The reconstruction square is required for every tuple,
so compatibility of the distinguished pilot is derived below.
-/
structure SourceFGloballyRealifiedTimesMuPrimeStripEquivalence
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta}
    (source target :
      SourceFGloballyRealifiedTimesMuPrimeStrip models) where
  global :
    SourceFrobenioidEquivalence
      source.global.globalFrobenioid target.global.globalFrobenioid
  prime : source.global.Prime ≃ target.global.Prime
  prime_compatible :
    ∀ value,
      target.global.primeEquivSelectedPlace (prime value) =
        source.global.primeEquivSelectedPlace value
  localEquivalence :
    SourceFTimesMuPrimeStripEquivalence
      source.localStrip target.localStrip
  characteristicLocal :
    ∀ v, TopologicalMonoidIso
      (source.global.characteristicLocal v)
      (target.global.characteristicLocal v)
  realifiedLocal :
    ∀ v, TopologicalMonoidIso
      (source.global.realifiedLocal v)
      (target.global.realifiedLocal v)
  rho_compatible :
    ∀ v value,
      (realifiedLocal v).toHom ((source.global.rho v).toHom value) =
        (target.global.rho v).toHom ((characteristicLocal v).toHom value)
  badGenerator_compatible :
    ∀ v : SourceFTimesMuBadPlace theta,
      (localEquivalence.finite v.1).coverPair.arithmeticMonoid
          (source.pilot.badGenerator v).1 =
        (target.pilot.badGenerator v).1
  characteristicCurrency_compatible :
    ∀ v : SourceFTimesMuBadPlace theta,
      (characteristicLocal
          (sourceTimesMuFiniteToSelectedPlace v.1)).toHom
          (source.pilot.characteristicCurrencyIso v
            (source.pilot.badGenerator v)) =
        target.pilot.characteristicCurrencyIso v
          ⟨(localEquivalence.finite v.1).coverPair.arithmeticMonoid
              (source.pilot.badGenerator v).1,
            ((localEquivalence.finite v.1).characteristic_compatible
              (source.pilot.badGenerator v).1).mp
                (source.pilot.badGenerator v).2⟩
  reconstruct_compatible :
    ∀ tuple :
        (∀ v : SourceFTimesMuBadPlace theta,
          (source.global.realifiedLocal
            (sourceTimesMuFiniteToSelectedPlace v.1)).carrier),
      global.carrier.functor.obj (source.pilot.reconstruct tuple) ≅
        target.pilot.reconstruct
          (fun v =>
            (realifiedLocal
              (sourceTimesMuFiniteToSelectedPlace v.1)).toHom (tuple v))
  arithmeticDegree_compatible :
    ∀ value : source.global.globalFrobenioid.carrier,
      target.pilot.arithmeticDegree (global.carrier.functor.obj value) =
        source.pilot.arithmeticDegree value

namespace SourceFGloballyRealifiedTimesMuPrimeStripEquivalence

variable
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta}
    {source middle target :
      SourceFGloballyRealifiedTimesMuPrimeStrip models}

/-- Identity globally realified isomorphism. -/
noncomputable def refl
    (source : SourceFGloballyRealifiedTimesMuPrimeStrip models) :
    SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source source where
  global := SourceFrobenioidEquivalence.refl _
  prime := Equiv.refl _
  prime_compatible _ := rfl
  localEquivalence :=
    SourceFTimesMuPrimeStripEquivalence.refl source.localStrip
  characteristicLocal v :=
    TopologicalMonoidIso.refl (source.global.characteristicLocal v)
  realifiedLocal v :=
    TopologicalMonoidIso.refl (source.global.realifiedLocal v)
  rho_compatible _ _ := rfl
  badGenerator_compatible _ := rfl
  characteristicCurrency_compatible _ := rfl
  reconstruct_compatible _ := Iso.refl _
  arithmeticDegree_compatible _ := rfl

/-- Composition of globally realified isomorphisms. -/
noncomputable def trans
    (first :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source middle)
    (second :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence middle target) :
    SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source target where
  global := first.global.trans second.global
  prime := first.prime.trans second.prime
  prime_compatible value := by
    change
      target.global.primeEquivSelectedPlace
          (second.prime (first.prime value)) = _
    rw [second.prime_compatible]
    rw [first.prime_compatible]
  localEquivalence :=
    first.localEquivalence.trans second.localEquivalence
  characteristicLocal v :=
    (first.characteristicLocal v).trans (second.characteristicLocal v)
  realifiedLocal v :=
    (first.realifiedLocal v).trans (second.realifiedLocal v)
  rho_compatible v value := by
    change
      (second.realifiedLocal v).toHom
          ((first.realifiedLocal v).toHom
            ((source.global.rho v).toHom value)) = _
    rw [first.rho_compatible]
    rw [second.rho_compatible]
    rfl
  badGenerator_compatible v := by
    change
      (second.localEquivalence.finite v.1).coverPair.arithmeticMonoid
          ((first.localEquivalence.finite v.1).coverPair.arithmeticMonoid
            (source.pilot.badGenerator v).1) = _
    rw [first.badGenerator_compatible]
    rw [second.badGenerator_compatible]
  characteristicCurrency_compatible v := by
    let firstMappedGenerator :
        (middle.localStrip.finite v.1).input.characteristic :=
      ⟨(first.localEquivalence.finite v.1).coverPair.arithmeticMonoid
          (source.pilot.badGenerator v).1,
        ((first.localEquivalence.finite v.1).characteristic_compatible
          (source.pilot.badGenerator v).1).mp
            (source.pilot.badGenerator v).2⟩
    have hgenerator :
        firstMappedGenerator = middle.pilot.badGenerator v := by
      apply Subtype.ext
      exact first.badGenerator_compatible v
    change
      (second.characteristicLocal _).toHom
          ((first.characteristicLocal _).toHom
            (source.pilot.characteristicCurrencyIso v
              (source.pilot.badGenerator v))) = _
    rw [first.characteristicCurrency_compatible]
    change
      (second.characteristicLocal _).toHom
          (middle.pilot.characteristicCurrencyIso v firstMappedGenerator) = _
    rw [hgenerator]
    rw [second.characteristicCurrency_compatible]
    apply congrArg (target.pilot.characteristicCurrencyIso v)
    apply Subtype.ext
    change
      (second.localEquivalence.finite v.1).coverPair.arithmeticMonoid
          (middle.pilot.badGenerator v).1 =
        (second.localEquivalence.finite v.1).coverPair.arithmeticMonoid
          ((first.localEquivalence.finite v.1).coverPair.arithmeticMonoid
            (source.pilot.badGenerator v).1)
    rw [first.badGenerator_compatible]
  reconstruct_compatible tuple :=
    second.global.carrier.functor.mapIso
        (first.reconstruct_compatible tuple) ≪≫
      second.reconstruct_compatible
        (fun v =>
          (first.realifiedLocal
            (sourceTimesMuFiniteToSelectedPlace v.1)).toHom (tuple v))
  arithmeticDegree_compatible value := by
    change
      target.pilot.arithmeticDegree
          (second.global.carrier.functor.obj
            (first.global.carrier.functor.obj value)) = _
    rw [second.arithmeticDegree_compatible]
    rw [first.arithmeticDegree_compatible]

/-- The realified bad-place character tuple commutes with a global isomorphism. -/
theorem localPilotCharacter_compatible
    (equivalence :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source target)
    (v : SourceFTimesMuBadPlace theta) :
    (equivalence.realifiedLocal
        (sourceTimesMuFiniteToSelectedPlace v.1)).toHom
        (source.pilot.localPilotCharacter v) =
      target.pilot.localPilotCharacter v := by
  rw [SourceFTimesMuPilotReconstruction.localPilotCharacter]
  rw [equivalence.rho_compatible]
  rw [equivalence.characteristicCurrency_compatible]
  let mappedGenerator :
      (target.localStrip.finite v.1).input.characteristic :=
    ⟨(equivalence.localEquivalence.finite v.1).coverPair.arithmeticMonoid
        (source.pilot.badGenerator v).1,
      ((equivalence.localEquivalence.finite v.1).characteristic_compatible
        (source.pilot.badGenerator v).1).mp
          (source.pilot.badGenerator v).2⟩
  have hgenerator : mappedGenerator = target.pilot.badGenerator v := by
    apply Subtype.ext
    exact equivalence.badGenerator_compatible v
  change
    (target.global.rho _).toHom
        (target.pilot.characteristicCurrencyIso v mappedGenerator) = _
  rw [hgenerator]
  rfl

/-- The distinguished pilot object is preserved up to global Frobenioid isomorphism. -/
noncomputable def pilotObjectIso
    (equivalence :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source target) :
    equivalence.global.carrier.functor.obj source.pilotObject ≅
      target.pilotObject := by
  let comparison :=
    equivalence.reconstruct_compatible source.pilot.localPilotCharacter
  have hcharacters :
      (fun v =>
        (equivalence.realifiedLocal
          (sourceTimesMuFiniteToSelectedPlace v.1)).toHom
            (source.pilot.localPilotCharacter v)) =
        target.pilot.localPilotCharacter := by
    funext v
    exact equivalence.localPilotCharacter_compatible v
  rw [hcharacters] at comparison
  exact comparison

/-- Arithmetic degree of the transported pilot equals the source pilot degree. -/
theorem pilotObject_arithmeticDegree_compatible
    (equivalence :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source target) :
    target.pilot.arithmeticDegree
        (equivalence.global.carrier.functor.obj source.pilotObject) =
      source.pilot.arithmeticDegree source.pilotObject :=
  equivalence.arithmeticDegree_compatible source.pilotObject

end SourceFGloballyRealifiedTimesMuPrimeStripEquivalence

end Iut
