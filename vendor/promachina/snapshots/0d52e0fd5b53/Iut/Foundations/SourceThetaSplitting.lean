/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceThetaEvaluation
import Mathlib.Algebra.Group.Submonoid.Pointwise
import Mathlib.GroupTheory.Torsion

/-!
# Splittings up to torsion for IUT II theta evaluation

This file formalizes the algebra in IUT II, Corollaries 2.6(ii), 2.8(iii),
and 3.5(iii).  The torsion subgroup is the actual torsion in the constant
subgroup.  A splitting up to torsion means that multiplication gives a
bijection from the quotient constant factor and the quotient theta-value set
onto their product set.
-/

namespace Iut

universe u

open scoped Pointwise

/-- The torsion elements in a specified subgroup of an abelian ambient group. -/
def sourceConstantTorsion
    {A : Type u} [CommGroup A]
    (constants : Subgroup A) :
    Subgroup A :=
  constants ⊓ CommGroup.torsion A

/--
For constants obtained from the unit Kummer embedding, the paper's
`M_TM^mu` is exactly the image of the torsion units.
-/
theorem sourceConstantTorsion_unitKummer
    {G : TopologicalGroupCat.{u}}
    [CompactSpace G]
    {A : Type u}
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [IsMulCommutative A]
    {coefficientAction : ContinuousGroupAction G A}
    (embedding :
      SourceIUTIIUnitKummerEmbedding
        G coefficientAction) :
    sourceConstantTorsion embedding.constantSubgroup =
      embedding.torsionUnitImage := by
  exact
    embedding.torsionUnitImage_eq_constant_torsion.symm

/-- The ambient group modulo the torsion in the constant subgroup. -/
abbrev SourceConstantTorsionQuotient
    {A : Type u} [CommGroup A]
    (constants : Subgroup A) :=
  A ⧸ sourceConstantTorsion constants

/-- The image of the constant subgroup after quotienting by its torsion. -/
def sourceQuotientConstantSubgroup
    {A : Type u} [CommGroup A]
    (constants : Subgroup A) :
    Subgroup (SourceConstantTorsionQuotient constants) :=
  constants.map
    (QuotientGroup.mk'
      (sourceConstantTorsion constants))

/-- The image of a theta-value set after quotienting by constant torsion. -/
def sourceQuotientThetaSet
    {A : Type u} [CommGroup A]
    (constants : Subgroup A)
    (thetaValues : Set A) :
    Set (SourceConstantTorsionQuotient constants) :=
  (QuotientGroup.mk'
    (sourceConstantTorsion constants)) '' thetaValues

/-- The product of quotient constants and quotient theta values. -/
def sourceQuotientConstantThetaProduct
    {A : Type u} [CommGroup A]
    (constants : Subgroup A)
    (thetaValues : Set A) :
    Set (SourceConstantTorsionQuotient constants) :=
  Set.image2 (· * ·)
    (sourceQuotientConstantSubgroup constants :
      Set (SourceConstantTorsionQuotient constants))
    (sourceQuotientThetaSet constants thetaValues)

/--
The multiplication parametrization whose bijectivity is the splitting up to
torsion asserted in IUT II.
-/
def sourceSplittingUpToTorsionMap
    {A : Type u} [CommGroup A]
    (constants : Subgroup A)
    (thetaValues : Set A) :
    sourceQuotientConstantSubgroup constants ×
        sourceQuotientThetaSet constants thetaValues →
      sourceQuotientConstantThetaProduct
        constants thetaValues :=
  fun input =>
    ⟨input.1.1 * input.2.1,
      ⟨input.1.1, input.1.2,
        input.2.1, input.2.2, rfl⟩⟩

/-- Exact predicate for a constant/theta splitting after quotienting torsion. -/
def SourceSplittingUpToTorsion
    {A : Type u} [CommGroup A]
    (constants : Subgroup A)
    (thetaValues : Set A) : Prop :=
  Function.Bijective
    (sourceSplittingUpToTorsionMap
      constants thetaValues)

/--
A multiplicative equivalence carries the torsion in a constant subgroup
exactly to the torsion in the transported constant subgroup.
-/
theorem sourceConstantTorsion_map
    {A B : Type u} [CommGroup A] [CommGroup B]
    (equivalence : A ≃* B)
    (constants : Subgroup A) :
    (sourceConstantTorsion constants).map
        equivalence.toMonoidHom =
      sourceConstantTorsion
        (constants.map equivalence.toMonoidHom) := by
  ext target
  constructor
  · rintro ⟨source, ⟨hconstant, htorsion⟩, rfl⟩
    constructor
    · exact ⟨source, hconstant, rfl⟩
    · exact
        equivalence.injective.isOfFinOrder_iff.mpr
          htorsion
  · rintro
      ⟨⟨source, hconstant, hsource⟩,
        htorsion⟩
    subst target
    refine
      ⟨source, ⟨hconstant, ?_⟩, rfl⟩
    exact
      equivalence.injective.isOfFinOrder_iff.mp
        htorsion

/-- The quotient equivalence induced by transport of constant torsion. -/
noncomputable def sourceConstantTorsionQuotientCongr
    {A B : Type u} [CommGroup A] [CommGroup B]
    (equivalence : A ≃* B)
    (constants : Subgroup A) :
    SourceConstantTorsionQuotient constants ≃*
      SourceConstantTorsionQuotient
        (constants.map equivalence.toMonoidHom) :=
  QuotientGroup.congr
    (sourceConstantTorsion constants)
    (sourceConstantTorsion
      (constants.map equivalence.toMonoidHom))
    equivalence
    (sourceConstantTorsion_map
      equivalence constants)

@[simp]
theorem sourceConstantTorsionQuotientCongr_mk
    {A B : Type u} [CommGroup A] [CommGroup B]
    (equivalence : A ≃* B)
    (constants : Subgroup A)
    (value : A) :
    sourceConstantTorsionQuotientCongr
        equivalence constants
        (QuotientGroup.mk' (sourceConstantTorsion constants)
          value) =
      QuotientGroup.mk'
        (sourceConstantTorsion
          (constants.map equivalence.toMonoidHom))
        (equivalence value) :=
  rfl

/--
The induced quotient equivalence carries the quotient constant subgroup onto
the quotient of the transported constant subgroup.
-/
theorem sourceQuotientConstantSubgroup_map
    {A B : Type u} [CommGroup A] [CommGroup B]
    (equivalence : A ≃* B)
    (constants : Subgroup A) :
    (sourceQuotientConstantSubgroup constants).map
        (sourceConstantTorsionQuotientCongr
          equivalence constants).toMonoidHom =
      sourceQuotientConstantSubgroup
        (constants.map equivalence.toMonoidHom) := by
  ext target
  constructor
  · rintro
      ⟨source,
        ⟨value, hconstant, hsource⟩,
        htarget⟩
    subst source
    subst target
    exact
      ⟨equivalence value,
        ⟨value, hconstant, rfl⟩, rfl⟩
  · rintro
      ⟨targetValue,
        ⟨sourceValue, hconstant, htargetValue⟩,
        htarget⟩
    subst targetValue
    subst target
    refine
      ⟨QuotientGroup.mk'
          (sourceConstantTorsion constants)
          sourceValue,
        ⟨sourceValue, hconstant, rfl⟩, rfl⟩

/--
The induced quotient equivalence carries the quotient theta-value set onto
the quotient of the transported theta-value set.
-/
theorem sourceQuotientThetaSet_image
    {A B : Type u} [CommGroup A] [CommGroup B]
    (equivalence : A ≃* B)
    (constants : Subgroup A)
    (thetaValues : Set A) :
    sourceConstantTorsionQuotientCongr
          equivalence constants ''
        sourceQuotientThetaSet
          constants thetaValues =
      sourceQuotientThetaSet
        (constants.map equivalence.toMonoidHom)
        (equivalence '' thetaValues) := by
  ext target
  constructor
  · rintro
      ⟨source,
        ⟨value, htheta, hsource⟩,
        htarget⟩
    subst source
    subst target
    exact
      ⟨equivalence value,
        ⟨value, htheta, rfl⟩, rfl⟩
  · rintro
      ⟨targetValue,
        ⟨sourceValue, htheta, htargetValue⟩,
        htarget⟩
    subst targetValue
    subst target
    exact
      ⟨QuotientGroup.mk'
          (sourceConstantTorsion constants)
          sourceValue,
        ⟨sourceValue, htheta, rfl⟩, rfl⟩

/-- Transport of the quotient constant factor through a restriction equivalence. -/
noncomputable def sourceQuotientConstantFactorCongr
    {A B : Type u} [CommGroup A] [CommGroup B]
    (equivalence : A ≃* B)
    (constants : Subgroup A) :
    sourceQuotientConstantSubgroup constants ≃
      sourceQuotientConstantSubgroup
        (constants.map equivalence.toMonoidHom) where
  toFun source :=
    ⟨sourceConstantTorsionQuotientCongr
        equivalence constants source.1,
      (sourceQuotientConstantSubgroup_map
        equivalence constants).le
        ⟨source.1, source.2, rfl⟩⟩
  invFun target :=
    ⟨(sourceConstantTorsionQuotientCongr
        equivalence constants).symm target.1,
      by
        have htarget :
            target.1 ∈
              (sourceQuotientConstantSubgroup constants).map
                (sourceConstantTorsionQuotientCongr
                  equivalence constants).toMonoidHom := by
          rw [sourceQuotientConstantSubgroup_map]
          exact target.2
        rcases htarget with
          ⟨source, hsource, hsourceTarget⟩
        have :
            (sourceConstantTorsionQuotientCongr
                equivalence constants).symm target.1 =
              source := by
          rw [← hsourceTarget]
          exact
            (sourceConstantTorsionQuotientCongr
              equivalence constants).symm_apply_apply source
        rw [this]
        exact hsource⟩
  left_inv source := by
    apply Subtype.ext
    exact
      (sourceConstantTorsionQuotientCongr
        equivalence constants).symm_apply_apply source.1
  right_inv target := by
    apply Subtype.ext
    exact
      (sourceConstantTorsionQuotientCongr
        equivalence constants).apply_symm_apply target.1

/-- Transport of the quotient theta-value factor through a restriction equivalence. -/
noncomputable def sourceQuotientThetaFactorCongr
    {A B : Type u} [CommGroup A] [CommGroup B]
    (equivalence : A ≃* B)
    (constants : Subgroup A)
    (thetaValues : Set A) :
    sourceQuotientThetaSet constants thetaValues ≃
      sourceQuotientThetaSet
        (constants.map equivalence.toMonoidHom)
        (equivalence '' thetaValues) where
  toFun source :=
    ⟨sourceConstantTorsionQuotientCongr
        equivalence constants source.1,
      (sourceQuotientThetaSet_image
        equivalence constants thetaValues).le
        ⟨source.1, source.2, rfl⟩⟩
  invFun target :=
    ⟨(sourceConstantTorsionQuotientCongr
        equivalence constants).symm target.1,
      by
        have htarget :
            target.1 ∈
                sourceConstantTorsionQuotientCongr
                    equivalence constants ''
                  sourceQuotientThetaSet
                    constants thetaValues := by
          rw [sourceQuotientThetaSet_image]
          exact target.2
        rcases htarget with
          ⟨source, hsource, hsourceTarget⟩
        have :
            (sourceConstantTorsionQuotientCongr
                equivalence constants).symm target.1 =
              source := by
          rw [← hsourceTarget]
          exact
            (sourceConstantTorsionQuotientCongr
              equivalence constants).symm_apply_apply source
        rw [this]
        exact hsource⟩
  left_inv source := by
    apply Subtype.ext
    exact
      (sourceConstantTorsionQuotientCongr
        equivalence constants).symm_apply_apply source.1
  right_inv target := by
    apply Subtype.ext
    exact
      (sourceConstantTorsionQuotientCongr
        equivalence constants).apply_symm_apply target.1

/-- Transport of both factors in a splitting up to torsion. -/
noncomputable def sourceSplittingFactorCongr
    {A B : Type u} [CommGroup A] [CommGroup B]
    (equivalence : A ≃* B)
    (constants : Subgroup A)
    (thetaValues : Set A) :
    sourceQuotientConstantSubgroup constants ×
        sourceQuotientThetaSet constants thetaValues ≃
      sourceQuotientConstantSubgroup
          (constants.map equivalence.toMonoidHom) ×
        sourceQuotientThetaSet
          (constants.map equivalence.toMonoidHom)
          (equivalence '' thetaValues) :=
  Equiv.prodCongr
    (sourceQuotientConstantFactorCongr
      equivalence constants)
    (sourceQuotientThetaFactorCongr
      equivalence constants thetaValues)

/--
Multiplication of the transported factors commutes with the quotient
equivalence.  This is the algebraic compatibility required of the restriction
isomorphisms in Corollary 3.5(iii).
-/
theorem sourceSplittingUpToTorsionMap_transport
    {A B : Type u} [CommGroup A] [CommGroup B]
    (equivalence : A ≃* B)
    (constants : Subgroup A)
    (thetaValues : Set A)
    (input :
      sourceQuotientConstantSubgroup constants ×
        sourceQuotientThetaSet constants thetaValues) :
    sourceConstantTorsionQuotientCongr
        equivalence constants
        (sourceSplittingUpToTorsionMap
          constants thetaValues input).1 =
      (sourceSplittingUpToTorsionMap
        (constants.map equivalence.toMonoidHom)
        (equivalence '' thetaValues)
        (sourceSplittingFactorCongr
          equivalence constants thetaValues input)).1 := by
  exact
    map_mul
      (sourceConstantTorsionQuotientCongr
        equivalence constants)
      input.1.1 input.2.1

/--
A splitting up to torsion is preserved by a multiplicative equivalence when
the constant subgroup and theta-value subset are transported by that same
equivalence.  Thus the Gaussian-side splitting in Corollary 3.5(iii) is a
consequence of the Proposition 3.1 splitting once the Corollary 2.8 restriction
isomorphism and its two factor identifications have been constructed.
-/
theorem SourceSplittingUpToTorsion.map
    {A B : Type u} [CommGroup A] [CommGroup B]
    {constants : Subgroup A}
    {thetaValues : Set A}
    (splitting :
      SourceSplittingUpToTorsion
        constants thetaValues)
    (equivalence : A ≃* B) :
    SourceSplittingUpToTorsion
      (constants.map equivalence.toMonoidHom)
      (equivalence '' thetaValues) := by
  constructor
  · intro first second hequal
    let factorEquivalence :=
      sourceSplittingFactorCongr
        equivalence constants thetaValues
    let firstSource :=
      factorEquivalence.symm first
    let secondSource :=
      factorEquivalence.symm second
    have hsourceOutputs :
        sourceSplittingUpToTorsionMap
            constants thetaValues firstSource =
          sourceSplittingUpToTorsionMap
            constants thetaValues secondSource := by
      apply Subtype.ext
      apply
        (sourceConstantTorsionQuotientCongr
          equivalence constants).injective
      rw [
        sourceSplittingUpToTorsionMap_transport,
        sourceSplittingUpToTorsionMap_transport]
      change
        (sourceSplittingUpToTorsionMap
            (constants.map equivalence.toMonoidHom)
            (equivalence '' thetaValues)
            (factorEquivalence firstSource)).1 =
          (sourceSplittingUpToTorsionMap
            (constants.map equivalence.toMonoidHom)
            (equivalence '' thetaValues)
            (factorEquivalence secondSource)).1
      rw [
        show factorEquivalence firstSource = first by
          exact factorEquivalence.apply_symm_apply first,
        show factorEquivalence secondSource = second by
          exact factorEquivalence.apply_symm_apply second]
      exact congrArg Subtype.val hequal
    have hsources :
        firstSource = secondSource :=
      splitting.1 hsourceOutputs
    calc
      first = factorEquivalence firstSource :=
        (factorEquivalence.apply_symm_apply first).symm
      _ = factorEquivalence secondSource :=
        congrArg factorEquivalence hsources
      _ = second :=
        factorEquivalence.apply_symm_apply second
  · rintro ⟨value, hvalue⟩
    rcases hvalue with
      ⟨constant, hconstant,
        theta, htheta, hproduct⟩
    refine
      ⟨(⟨constant, hconstant⟩,
        ⟨theta, htheta⟩), ?_⟩
    apply Subtype.ext
    exact hproduct

theorem sourceSplittingUpToTorsionMap_surjective
    {A : Type u} [CommGroup A]
    (constants : Subgroup A)
    (thetaValues : Set A) :
    Function.Surjective
      (sourceSplittingUpToTorsionMap
        constants thetaValues) := by
  rintro ⟨value, hValue⟩
  rcases hValue with
    ⟨constant, hConstant, theta, hTheta, hProduct⟩
  refine
    ⟨(⟨constant, hConstant⟩,
      ⟨theta, hTheta⟩), ?_⟩
  apply Subtype.ext
  exact hProduct

/-- The diagonal subgroup of constants in a labeled product of commutative groups. -/
def sourceDiagonalConstantSubgroup
    {I M : Type u} [CommGroup M] :
    Subgroup (I → M) :=
  (Pi.monoidHom
    (fun _ : I => MonoidHom.id M)).range

/-- The natural-power theta-value subset `xi^N` in Corollary 3.5(ii),(iii). -/
def sourceFiniteGaussianThetaSet
    {I M : Type u} [CommGroup M]
    (profile : I → M) :
    Set (I → M) :=
  Submonoid.powers profile

/-- The rational-power theta-value subset `xi^Q>=0` in Corollary 3.5(ii),(iii). -/
def sourceInfiniteGaussianThetaSet
    {I M : Type u} [CommGroup M]
    {profile : I → M}
    (roots : ValueProfileRootSystem profile) :
    Set (I → M) :=
  valueProfileRationalPowers roots

/-- Splitting up to torsion of the finite Gaussian monoid factors. -/
def SourceFiniteGaussianSplittingUpToTorsion
    {I M : Type u} [CommGroup M]
    (profile : I → M) : Prop :=
  SourceSplittingUpToTorsion
    sourceDiagonalConstantSubgroup
    (sourceFiniteGaussianThetaSet profile)

/-- Splitting up to torsion of the infinite Gaussian monoid factors. -/
def SourceInfiniteGaussianSplittingUpToTorsion
    {I M : Type u} [CommGroup M]
    {profile : I → M}
    (roots : ValueProfileRootSystem profile) : Prop :=
  SourceSplittingUpToTorsion
    sourceDiagonalConstantSubgroup
    (sourceInfiniteGaussianThetaSet roots)

/--
For a commutative group, the diagonal subgroup of constants has exactly the
same carrier as the diagonal-unit submonoid used to define the Gaussian
monoid.
-/
theorem sourceDiagonalConstantSubgroup_toSubmonoid_eq
    {I M : Type u} [CommGroup M] :
    (sourceDiagonalConstantSubgroup :
        Subgroup (I → M)).toSubmonoid =
      diagonalConstantUnitSubmonoid := by
  ext profile
  constructor
  · rintro ⟨constant, hconstant⟩
    refine ⟨toUnits constant, ?_⟩
    rw [← hconstant]
    rfl
  · rintro ⟨constant, hconstant⟩
    refine ⟨(constant : M), ?_⟩
    rw [← hconstant]
    rfl

/-- The finite Gaussian monoid is generated by precisely its two splitting factors. -/
theorem sourceGaussianMonoid_eq_splittingFactors
    {I M : Type u} [CommGroup M]
    (profile : I → M) :
    sourceGaussianMonoid profile =
      (sourceDiagonalConstantSubgroup :
          Subgroup (I → M)).toSubmonoid ⊔
        Submonoid.powers profile := by
  rw [sourceGaussianMonoid,
    sourceDiagonalConstantSubgroup_toSubmonoid_eq]
  exact congrArg
    (diagonalConstantUnitSubmonoid ⊔ ·)
    (Submonoid.powers_eq_closure profile).symm

/--
The carrier of the finite Gaussian monoid is the pointwise product of the
constant factor and `xi^N`, as displayed in Corollary 3.5(iii).
-/
theorem sourceGaussianMonoid_carrier_eq_splittingFactorProduct
    {I M : Type u} [CommGroup M]
    (profile : I → M) :
    (sourceGaussianMonoid profile :
        Set (I → M)) =
      (sourceDiagonalConstantSubgroup
          (I := I) (M := M) :
          Set (I → M)) *
        sourceFiniteGaussianThetaSet profile := by
  rw [sourceGaussianMonoid_eq_splittingFactors]
  exact
    Submonoid.coe_sup
      (sourceDiagonalConstantSubgroup :
        Subgroup (I → M)).toSubmonoid
      (Submonoid.powers profile)

/-- The infinite Gaussian monoid is generated by its two splitting factors. -/
theorem sourceInfiniteGaussianMonoid_eq_splittingFactors
    {I M : Type u} [CommGroup M]
    {profile : I → M}
    (roots : ValueProfileRootSystem profile) :
    sourceInfiniteGaussianMonoid roots =
      (sourceDiagonalConstantSubgroup :
          Subgroup (I → M)).toSubmonoid ⊔
        valueProfileRationalPowers roots := by
  rw [sourceInfiniteGaussianMonoid,
    sourceDiagonalConstantSubgroup_toSubmonoid_eq]

/--
The carrier of the infinite Gaussian monoid is the pointwise product of the
constant factor and `xi^Q>=0`.
-/
theorem sourceInfiniteGaussianMonoid_carrier_eq_splittingFactorProduct
    {I M : Type u} [CommGroup M]
    {profile : I → M}
    (roots : ValueProfileRootSystem profile) :
    (sourceInfiniteGaussianMonoid roots :
        Set (I → M)) =
      (sourceDiagonalConstantSubgroup
          (I := I) (M := M) :
          Set (I → M)) *
        sourceInfiniteGaussianThetaSet roots := by
  rw [sourceInfiniteGaussianMonoid_eq_splittingFactors]
  exact
    Submonoid.coe_sup
      (sourceDiagonalConstantSubgroup :
        Subgroup (I → M)).toSubmonoid
      (valueProfileRationalPowers roots)

/--
Finite Gaussian specialization of Corollary 3.5(iii): the Proposition 3.1
splitting transports to `Psi_xi` once the actual restriction equivalence sends
the two source factors to the diagonal constants and `xi^N`.
-/
theorem sourceCorollary35FiniteGaussianSplittingOfProposition31
    {A I M : Type u}
    [CommGroup A] [CommGroup M]
    {constants : Subgroup A}
    {thetaValues : Set A}
    (splitting :
      SourceSplittingUpToTorsion
        constants thetaValues)
    (restriction : A ≃* (I → M))
    (constants_restrict :
      constants.map restriction.toMonoidHom =
        sourceDiagonalConstantSubgroup)
    (profile : I → M)
    (theta_restrict :
      restriction '' thetaValues =
        sourceFiniteGaussianThetaSet
          (I := I) (M := M) profile) :
    SourceFiniteGaussianSplittingUpToTorsion
      profile := by
  have transported :=
    splitting.map restriction
  rw [constants_restrict, theta_restrict] at transported
  exact transported

/--
Infinite Gaussian specialization of Corollary 3.5(iii): the same restriction
equivalence transports the Proposition 3.1 splitting to
`infinity-Psi_xi` when it identifies the theta factor with `xi^Q>=0`.
-/
theorem sourceCorollary35InfiniteGaussianSplittingOfProposition31
    {A I M : Type u}
    [CommGroup A] [CommGroup M]
    {constants : Subgroup A}
    {thetaValues : Set A}
    (splitting :
      SourceSplittingUpToTorsion
        constants thetaValues)
    (restriction : A ≃* (I → M))
    (constants_restrict :
      constants.map restriction.toMonoidHom =
        sourceDiagonalConstantSubgroup)
    {profile : I → M}
    (roots : ValueProfileRootSystem profile)
    (theta_restrict :
      restriction '' thetaValues =
        sourceInfiniteGaussianThetaSet roots) :
    SourceInfiniteGaussianSplittingUpToTorsion
      roots := by
  have transported :=
    splitting.map restriction
  rw [constants_restrict, theta_restrict] at transported
  exact transported

/--
The restriction-theoretic input used in IUT II, Corollaries 1.12(ii), 2.6(ii),
2.8(iii), and Proposition 3.1(i).

Theta values restrict to torsion, while restriction detects torsion on the
constant subgroup.  These are the two source facts from which the splitting is
derived; bijectivity is not stored as an additional field.
-/
structure SourceTorsionDetectingRestriction
    {A B : Type u} [CommGroup A] [CommGroup B]
    (constants : Subgroup A)
    (thetaValues : Set A) where
  restriction : A →* B
  theta_restricts_to_torsion :
    ∀ {theta}, theta ∈ thetaValues →
      restriction theta ∈ CommGroup.torsion B
  detects_constant_torsion :
    ∀ {constant}, constant ∈ constants →
      restriction constant ∈ CommGroup.torsion B →
      constant ∈ sourceConstantTorsion constants

namespace SourceTorsionDetectingRestriction

variable
  {A B : Type u} [CommGroup A] [CommGroup B]
  {constants : Subgroup A}
  {thetaValues : Set A}

/--
The restriction criterion proves the characteristic splitting up to torsion.
This is the algebraic step invoked by Corollaries 1.12(ii), 2.6(ii), 2.8(iii),
and Proposition 3.1(i).
-/
theorem splittingUpToTorsion :
    SourceTorsionDetectingRestriction (B := B)
        constants thetaValues →
    SourceSplittingUpToTorsion
      constants thetaValues := by
  intro data
  constructor
  · intro first second hequal
    rcases first.1.2 with
      ⟨firstConstant, hfirstConstant,
        hfirstConstantQuotient⟩
    rcases second.1.2 with
      ⟨secondConstant, hsecondConstant,
        hsecondConstantQuotient⟩
    rcases first.2.2 with
      ⟨firstTheta, hfirstTheta,
        hfirstThetaQuotient⟩
    rcases second.2.2 with
      ⟨secondTheta, hsecondTheta,
        hsecondThetaQuotient⟩
    have hproductQuotient :
        QuotientGroup.mk'
              (sourceConstantTorsion constants)
              (firstConstant * firstTheta) =
          QuotientGroup.mk'
              (sourceConstantTorsion constants)
              (secondConstant * secondTheta) := by
      have hvalues :=
        congrArg Subtype.val hequal
      change
        first.1.1 * first.2.1 =
          second.1.1 * second.2.1 at hvalues
      rw [← hfirstConstantQuotient,
        ← hfirstThetaQuotient,
        ← hsecondConstantQuotient,
        ← hsecondThetaQuotient] at hvalues
      exact hvalues
    have hproductRatio :
        (firstConstant * firstTheta) /
            (secondConstant * secondTheta) ∈
          sourceConstantTorsion constants :=
      QuotientGroup.eq_iff_div_mem.mp
        hproductQuotient
    have hrestrictedProductRatio :
        data.restriction
              ((firstConstant * firstTheta) /
                (secondConstant * secondTheta)) ∈
          CommGroup.torsion B :=
      data.restriction.isOfFinOrder
        hproductRatio.2
    have hrestrictedThetaRatio :
        data.restriction
              (firstTheta / secondTheta) ∈
          CommGroup.torsion B := by
      rw [map_div]
      exact
        (CommGroup.torsion B).div_mem
          (data.theta_restricts_to_torsion
            hfirstTheta)
          (data.theta_restricts_to_torsion
            hsecondTheta)
    have hconstantRatio :
        firstConstant / secondConstant ∈
          sourceConstantTorsion constants := by
      apply data.detects_constant_torsion
      · exact constants.div_mem
          hfirstConstant hsecondConstant
      · have hidentity :
            data.restriction
                (firstConstant / secondConstant) =
              data.restriction
                  ((firstConstant * firstTheta) /
                    (secondConstant * secondTheta)) /
                data.restriction
                  (firstTheta / secondTheta) := by
          simp only [map_div, map_mul]
          simp [div_eq_mul_inv, mul_comm,
            mul_left_comm, mul_assoc]
        rw [hidentity]
        exact
          (CommGroup.torsion B).div_mem
            hrestrictedProductRatio
            hrestrictedThetaRatio
    have hconstantQuotient :
        QuotientGroup.mk'
              (sourceConstantTorsion constants)
              firstConstant =
          QuotientGroup.mk'
              (sourceConstantTorsion constants)
              secondConstant :=
      QuotientGroup.eq_iff_div_mem.mpr
        hconstantRatio
    have hthetaQuotient :
        QuotientGroup.mk'
              (sourceConstantTorsion constants)
              firstTheta =
          QuotientGroup.mk'
              (sourceConstantTorsion constants)
              secondTheta := by
      have hproducts :
          QuotientGroup.mk'
                (sourceConstantTorsion constants)
                firstConstant *
              QuotientGroup.mk'
                (sourceConstantTorsion constants)
                firstTheta =
            QuotientGroup.mk'
                (sourceConstantTorsion constants)
                secondConstant *
              QuotientGroup.mk'
                (sourceConstantTorsion constants)
                secondTheta := by
        simpa only [map_mul] using
          hproductQuotient
      rw [hconstantQuotient] at hproducts
      exact mul_left_cancel hproducts
    apply Prod.ext
    · apply Subtype.ext
      rw [← hfirstConstantQuotient,
        ← hsecondConstantQuotient]
      exact hconstantQuotient
    · apply Subtype.ext
      rw [← hfirstThetaQuotient,
        ← hsecondThetaQuotient]
      exact hthetaQuotient
  · exact
      sourceSplittingUpToTorsionMap_surjective
        constants thetaValues

end SourceTorsionDetectingRestriction

/--
A pointed inversion automorphism in the form used by IUT II,
Corollary 1.12(i).  The automorphism has order two modulo inner
automorphisms from the geometric subgroup, and it preserves the conjugacy
class of the pointed decomposition subgroup.
-/
structure SourceIUTIIPointedInversion
    (G : TopologicalGroupCat.{u}) where
  geometricSubgroup : Subgroup G
  geometricSubgroup_normal : geometricSubgroup.Normal
  inversion : ContinuousAutomorphism G
  inversion_preserves_geometric :
    geometricSubgroup.map
        inversion.toMulEquiv.toMonoidHom =
      geometricSubgroup
  inversion_sq_geometric_inner :
    inversion * inversion ∈
      geometricSubgroup.map
        (ContinuousAutomorphism.innerHom G)
  decompositionGroup : Subgroup G
  inversion_preserves_decomposition_class :
    SubgroupsConjugateBy
      geometricSubgroup
      decompositionGroup
      (decompositionGroup.map
        inversion.toMulEquiv.toMonoidHom)

namespace SourceIUTIIPointedInversion

variable {G : TopologicalGroupCat.{u}}

instance (pointed : SourceIUTIIPointedInversion G) :
    pointed.geometricSubgroup.Normal :=
  pointed.geometricSubgroup_normal

/-- The pointed decomposition subgroup with its induced topology. -/
def decompositionGroupObject
    (pointed : SourceIUTIIPointedInversion G) :
    TopologicalGroupCat.{u} :=
  TopologicalGroupCat.ofSubgroup
    G pointed.decompositionGroup

/-- The actual continuous inclusion used for restriction in cohomology. -/
def decompositionInclusion
    (pointed : SourceIUTIIPointedInversion G) :
    pointed.decompositionGroupObject ⟶ G :=
  TopologicalGroupCat.subgroupInclusion
    G pointed.decompositionGroup

end SourceIUTIIPointedInversion

/--
The restriction assertion of IUT II, Corollary 1.12(ii), stated on the actual
decomposition-subgroup inclusion associated to a pointed inversion.

The inverse image of target torsion on the constant subgroup is recorded as
an equality of subgroups.  Thus the weaker torsion-detection implication used
by the algebraic splitting proof is derived, not accepted as a field.
-/
structure SourceIUTIICorollary112PointedRestriction
    {G : TopologicalGroupCat.{u}}
    {A : Type u}
    [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [IsMulCommutative A]
    (coefficientAction : ContinuousGroupAction G A)
    (constants :
      Subgroup (ContinuousH1Germ coefficientAction))
    (thetaValues :
      Set (ContinuousH1Germ coefficientAction)) where
  pointed : SourceIUTIIPointedInversion G
  theta_restricts_to_torsion :
    ∀ {theta}, theta ∈ thetaValues →
      ContinuousH1Germ.restrict
          pointed.decompositionInclusion theta ∈
        CommGroup.torsion
          (ContinuousH1Germ
            (coefficientAction.comap
              pointed.decompositionInclusion))
  constant_torsion_preimage :
    constants ⊓
        Subgroup.comap
          (ContinuousH1Germ.restrictMonoidHom
            pointed.decompositionInclusion)
          (CommGroup.torsion
            (ContinuousH1Germ
              (coefficientAction.comap
                pointed.decompositionInclusion))) =
      sourceConstantTorsion constants

namespace SourceIUTIICorollary112PointedRestriction

variable
  {G : TopologicalGroupCat.{u}}
  {A : Type u}
  [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [IsMulCommutative A]
  {coefficientAction : ContinuousGroupAction G A}
  {constants :
    Subgroup (ContinuousH1Germ coefficientAction)}
  {thetaValues :
    Set (ContinuousH1Germ coefficientAction)}

/-- Corollary 1.12(ii)'s subgroup equality implies torsion detection. -/
theorem detects_constant_torsion
    (restriction :
      SourceIUTIICorollary112PointedRestriction
        coefficientAction constants thetaValues)
    {constant : ContinuousH1Germ coefficientAction}
    (constant_mem : constant ∈ constants)
    (restricted_torsion :
      ContinuousH1Germ.restrict
          restriction.pointed.decompositionInclusion
          constant ∈
        CommGroup.torsion
          (ContinuousH1Germ
            (coefficientAction.comap
              restriction.pointed.decompositionInclusion))) :
    constant ∈ sourceConstantTorsion constants := by
  have preimage_mem :
      constant ∈
        constants ⊓
          Subgroup.comap
            (ContinuousH1Germ.restrictMonoidHom
              restriction.pointed.decompositionInclusion)
            (CommGroup.torsion
              (ContinuousH1Germ
                (coefficientAction.comap
                  restriction.pointed.decompositionInclusion))) :=
    ⟨constant_mem, restricted_torsion⟩
  rw [restriction.constant_torsion_preimage]
    at preimage_mem
  exact preimage_mem

/-- Forget only the pointed source structure after deriving its consequence. -/
def toTorsionDetectingRestriction
    (restriction :
      SourceIUTIICorollary112PointedRestriction
        coefficientAction constants thetaValues) :
    SourceTorsionDetectingRestriction
      (B :=
        ContinuousH1Germ
          (coefficientAction.comap
            restriction.pointed.decompositionInclusion))
      constants thetaValues where
  restriction :=
    ContinuousH1Germ.restrictMonoidHom
      restriction.pointed.decompositionInclusion
  theta_restricts_to_torsion :=
    restriction.theta_restricts_to_torsion
  detects_constant_torsion := by
    intro constant constant_mem restricted_torsion
    exact restriction.detects_constant_torsion
      constant_mem restricted_torsion

/--
The Corollary 1.12(ii) splitting derived from the pointed decomposition-group
restriction and its exact inverse-image theorem.
-/
theorem splittingUpToTorsion
    (restriction :
      SourceIUTIICorollary112PointedRestriction
        coefficientAction constants thetaValues) :
    SourceSplittingUpToTorsion
      constants thetaValues :=
  restriction.toTorsionDetectingRestriction.splittingUpToTorsion

end SourceIUTIICorollary112PointedRestriction

/--
The finite Corollary 3.5(iii) splitting derived from the full two-stage source
mechanism: torsion-detecting restriction constructs the Proposition 3.1
splitting, then the Gaussian restriction equivalence transports it.
-/
theorem sourceCorollary35FiniteGaussianSplittingOfRestrictionData
    {A B I M : Type u}
    [CommGroup A] [CommGroup B] [CommGroup M]
    {constants : Subgroup A}
    {thetaValues : Set A}
    (proposition31Restriction :
      SourceTorsionDetectingRestriction (B := B)
        constants thetaValues)
    (gaussianRestriction : A ≃* (I → M))
    (constants_restrict :
      constants.map gaussianRestriction.toMonoidHom =
        sourceDiagonalConstantSubgroup)
    (profile : I → M)
    (theta_restrict :
      gaussianRestriction '' thetaValues =
        sourceFiniteGaussianThetaSet profile) :
    SourceFiniteGaussianSplittingUpToTorsion
      profile :=
  sourceCorollary35FiniteGaussianSplittingOfProposition31
    proposition31Restriction.splittingUpToTorsion
    gaussianRestriction constants_restrict
    profile theta_restrict

/--
The infinite Corollary 3.5(iii) splitting derived from the same two-stage
restriction mechanism.
-/
theorem sourceCorollary35InfiniteGaussianSplittingOfRestrictionData
    {A B I M : Type u}
    [CommGroup A] [CommGroup B] [CommGroup M]
    {constants : Subgroup A}
    {thetaValues : Set A}
    (proposition31Restriction :
      SourceTorsionDetectingRestriction (B := B)
        constants thetaValues)
    (gaussianRestriction : A ≃* (I → M))
    (constants_restrict :
      constants.map gaussianRestriction.toMonoidHom =
        sourceDiagonalConstantSubgroup)
    {profile : I → M}
    (roots : ValueProfileRootSystem profile)
    (theta_restrict :
      gaussianRestriction '' thetaValues =
        sourceInfiniteGaussianThetaSet roots) :
    SourceInfiniteGaussianSplittingUpToTorsion
      roots :=
  sourceCorollary35InfiniteGaussianSplittingOfProposition31
    proposition31Restriction.splittingUpToTorsion
    gaussianRestriction constants_restrict
    roots theta_restrict

namespace SourceIUTIICorollary28RestrictionStages

variable
  {G H K A Mu2l Mu : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [IsMulCommutative A]
  {l : PrimeGeFive}
  {action : ContinuousGroupAction G A}
  {firstRestriction : H →ₜ* G}
  {secondRestriction : K →ₜ* H}
  [Group Mu2l] [Group Mu]
  [MulAction Mu2l (ContinuousH1Germ action)]
  [MulAction Mu
    (ContinuousH1Germ action)]
  [MulAction Mu2l
    (ContinuousH1Germ (action.comap firstRestriction))]
  [MulAction Mu
    (ContinuousH1Germ (action.comap firstRestriction))]
  [MulAction Mu2l
    (ContinuousH1Germ
      ((action.comap firstRestriction).comap
        secondRestriction))]
  [MulAction Mu
    (ContinuousH1Germ
      ((action.comap firstRestriction).comap
        secondRestriction))]

variable
  (stages :
    SourceIUTIICorollary28RestrictionStages
      (G := G) (H := H) (K := K) (A := A)
      (Mu2l := Mu2l) (Mu := Mu)
      l action firstRestriction secondRestriction)

/--
At the zero label, the full final finite-theta orbit is torsion.  The common
`2l` exponent is forgotten only after it proves finite order.
-/
theorem afterSecond_zero_theta_carrier_subset_torsion
    (multiplicative :
      SourceIUTIIMultiplicativeTorsionAction
        l Mu2l
        (ContinuousH1Germ
          ((action.comap firstRestriction).comap
            secondRestriction)))
    (theta_zero :
      (stages.ambient.theta
        IUTIIAbsoluteThetaLabel.zero).representative =
          1) :
    ((stages.afterSecond).theta
        IUTIIAbsoluteThetaLabel.zero).carrier ⊆
      CommGroup.torsion
        (ContinuousH1Germ
          ((action.comap firstRestriction).comap
            secondRestriction)) := by
  apply
    multiplicative.toFiniteOrderAction
      |>.orbitCarrier_subset_torsion
  rw [stages.afterSecond_theta_representative,
    theta_zero]
  simp

/--
At the zero label, the full final infinite-theta orbit is torsion, not merely
its selected representative.  This follows from the identity representative
and the multiplicative finite-order `mu` action.
-/
theorem afterSecond_zero_infiniteTheta_carrier_subset_torsion
    (multiplicative :
      SourceIUTIIMultiplicativeFiniteOrderAction
        Mu
        (ContinuousH1Germ
          ((action.comap firstRestriction).comap
            secondRestriction)))
    (infiniteTheta_zero :
      (stages.ambient.infiniteTheta
        IUTIIAbsoluteThetaLabel.zero).representative =
          1) :
    ((stages.afterSecond).infiniteTheta
        IUTIIAbsoluteThetaLabel.zero).carrier ⊆
      CommGroup.torsion
      (ContinuousH1Germ
        ((action.comap firstRestriction).comap
          secondRestriction)) := by
  apply multiplicative.orbitCarrier_subset_torsion
  rw [stages.afterSecond_infiniteTheta_representative,
    infiniteTheta_zero]
  simp

/--
The finite-theta analogue of the Corollary 2.8(iii) restriction datum.
-/
def zeroThetaTorsionDetectingRestriction
    (constants :
      Subgroup (ContinuousH1Germ action))
    (multiplicative :
      SourceIUTIIMultiplicativeTorsionAction
        l Mu2l
        (ContinuousH1Germ
          ((action.comap firstRestriction).comap
            secondRestriction)))
    (theta_zero :
      (stages.ambient.theta
        IUTIIAbsoluteThetaLabel.zero).representative =
          1)
    (detects_constant_torsion :
      ∀ {constant},
        constant ∈ constants →
        SourceIUTIICorollary28RestrictionStages.totalRestrictionMonoidHom
              (action := action)
              (firstRestriction := firstRestriction)
              (secondRestriction := secondRestriction)
              constant ∈
          CommGroup.torsion
            (ContinuousH1Germ
              ((action.comap firstRestriction).comap
                secondRestriction)) →
        constant ∈ sourceConstantTorsion constants) :
    SourceTorsionDetectingRestriction
      (B :=
        ContinuousH1Germ
          ((action.comap firstRestriction).comap
            secondRestriction))
      constants
      ((stages.ambient.theta
        IUTIIAbsoluteThetaLabel.zero).carrier) where
  restriction :=
    SourceIUTIICorollary28RestrictionStages.totalRestrictionMonoidHom
      (action := action)
      (firstRestriction := firstRestriction)
      (secondRestriction := secondRestriction)
  theta_restricts_to_torsion := by
    intro theta htheta
    apply
      stages.afterSecond_zero_theta_carrier_subset_torsion
        multiplicative theta_zero
    exact
      stages.totalRestriction_mem_afterSecond_theta_carrier
        IUTIIAbsoluteThetaLabel.zero htheta
  detects_constant_torsion :=
    detects_constant_torsion

/--
The Corollary 2.8(iii) torsion-detecting restriction datum on the zero-labeled
infinite-theta orbit.  The theta-to-torsion property is derived from the actual
two-stage `H¹` restriction.  Torsion detection on constants is the remaining
input supplied by the source construction of `M_TM^x`.
-/
def zeroInfiniteThetaTorsionDetectingRestriction
    (constants :
      Subgroup (ContinuousH1Germ action))
    (multiplicative :
      SourceIUTIIMultiplicativeFiniteOrderAction
        Mu
        (ContinuousH1Germ
          ((action.comap firstRestriction).comap
            secondRestriction)))
    (infiniteTheta_zero :
      (stages.ambient.infiniteTheta
        IUTIIAbsoluteThetaLabel.zero).representative =
          1)
    (detects_constant_torsion :
      ∀ {constant},
        constant ∈ constants →
        SourceIUTIICorollary28RestrictionStages.totalRestrictionMonoidHom
              (action := action)
              (firstRestriction := firstRestriction)
              (secondRestriction := secondRestriction)
              constant ∈
          CommGroup.torsion
            (ContinuousH1Germ
              ((action.comap firstRestriction).comap
                secondRestriction)) →
        constant ∈ sourceConstantTorsion constants) :
    SourceTorsionDetectingRestriction
      (B :=
        ContinuousH1Germ
          ((action.comap firstRestriction).comap
            secondRestriction))
      constants
      ((stages.ambient.infiniteTheta
        IUTIIAbsoluteThetaLabel.zero).carrier) where
  restriction :=
    SourceIUTIICorollary28RestrictionStages.totalRestrictionMonoidHom
      (action := action)
      (firstRestriction := firstRestriction)
      (secondRestriction := secondRestriction)
  theta_restricts_to_torsion := by
    intro theta htheta
    apply
      stages.afterSecond_zero_infiniteTheta_carrier_subset_torsion
        multiplicative infiniteTheta_zero
    exact
      stages.totalRestriction_mem_afterSecond_infiniteTheta_carrier
        IUTIIAbsoluteThetaLabel.zero htheta
  detects_constant_torsion :=
    detects_constant_torsion

/-- The finite zero-label splitting derived from the composite restriction. -/
theorem zeroThetaSplittingUpToTorsion
    (constants :
      Subgroup (ContinuousH1Germ action))
    (multiplicative :
      SourceIUTIIMultiplicativeTorsionAction
        l Mu2l
        (ContinuousH1Germ
          ((action.comap firstRestriction).comap
            secondRestriction)))
    (theta_zero :
      (stages.ambient.theta
        IUTIIAbsoluteThetaLabel.zero).representative =
          1)
    (detects_constant_torsion :
      ∀ {constant},
        constant ∈ constants →
        SourceIUTIICorollary28RestrictionStages.totalRestrictionMonoidHom
              (action := action)
              (firstRestriction := firstRestriction)
              (secondRestriction := secondRestriction)
              constant ∈
          CommGroup.torsion
            (ContinuousH1Germ
              ((action.comap firstRestriction).comap
                secondRestriction)) →
        constant ∈ sourceConstantTorsion constants) :
    SourceSplittingUpToTorsion
      constants
      ((stages.ambient.theta
        IUTIIAbsoluteThetaLabel.zero).carrier) :=
  (stages.zeroThetaTorsionDetectingRestriction
    constants multiplicative theta_zero
    detects_constant_torsion).splittingUpToTorsion

/--
Corollary 2.8(iii)'s zero-label splitting, derived from the actual composite
restriction and its constant-torsion detection property.
-/
theorem zeroInfiniteThetaSplittingUpToTorsion
    (constants :
      Subgroup (ContinuousH1Germ action))
    (multiplicative :
      SourceIUTIIMultiplicativeFiniteOrderAction
        Mu
        (ContinuousH1Germ
          ((action.comap firstRestriction).comap
            secondRestriction)))
    (infiniteTheta_zero :
      (stages.ambient.infiniteTheta
        IUTIIAbsoluteThetaLabel.zero).representative =
          1)
    (detects_constant_torsion :
      ∀ {constant},
        constant ∈ constants →
        SourceIUTIICorollary28RestrictionStages.totalRestrictionMonoidHom
              (action := action)
              (firstRestriction := firstRestriction)
              (secondRestriction := secondRestriction)
              constant ∈
          CommGroup.torsion
            (ContinuousH1Germ
              ((action.comap firstRestriction).comap
                secondRestriction)) →
        constant ∈ sourceConstantTorsion constants) :
    SourceSplittingUpToTorsion
      constants
      ((stages.ambient.infiniteTheta
        IUTIIAbsoluteThetaLabel.zero).carrier) :=
  (stages.zeroInfiniteThetaTorsionDetectingRestriction
    constants multiplicative infiniteTheta_zero
    detects_constant_torsion).splittingUpToTorsion

end SourceIUTIICorollary28RestrictionStages

theorem sourceQuotientThetaSet_eq_one
    {A : Type u} [CommGroup A]
    {constants : Subgroup A}
    {thetaValues : Set A}
    (theta_is_torsion :
      thetaValues ⊆ sourceConstantTorsion constants)
    (value :
      sourceQuotientThetaSet constants thetaValues) :
    value.1 = 1 := by
  rcases value.2 with ⟨theta, hTheta, hValue⟩
  rw [← hValue]
  exact
    (QuotientGroup.eq_one_iff theta).2
      (theta_is_torsion hTheta)

/--
At a zero-labeled evaluation point, every theta value is constant torsion.
Consequently multiplication by the quotient theta factor is multiplication by
the identity, and the splitting up to torsion is canonical.
-/
theorem sourceZeroLabelSplittingUpToTorsion
    {A : Type u} [CommGroup A]
    (constants : Subgroup A)
    (thetaValues : Set A)
    (theta_is_torsion :
      thetaValues ⊆ sourceConstantTorsion constants) :
    SourceSplittingUpToTorsion
      constants thetaValues := by
  constructor
  · intro first second h
    apply Prod.ext
    · apply Subtype.ext
      have hValues :=
        congrArg Subtype.val h
      change
        first.1.1 * first.2.1 =
          second.1.1 * second.2.1 at hValues
      rw [sourceQuotientThetaSet_eq_one
          theta_is_torsion first.2,
        sourceQuotientThetaSet_eq_one
          theta_is_torsion second.2] at hValues
      simpa using hValues
    · apply Subtype.ext
      exact
        (sourceQuotientThetaSet_eq_one
          theta_is_torsion first.2).trans
        (sourceQuotientThetaSet_eq_one
          theta_is_torsion second.2).symm
  · exact
      sourceSplittingUpToTorsionMap_surjective
        constants thetaValues

/--
The zero-labeled constant action pair and its comparison with the chosen base
of the nonzero symmetrized family in IUT II, Corollary 3.5(iii).
-/
structure SourceIUTIIZeroLabelConstantComparison
    {l : PrimeGeFive}
    (symmetry :
      SourceIUTIISymmetrizingIsomorphisms.{u} l) where
  zeroPair :
    SourceTopologicalGroupMonoidActionPair.{u}
  zeroToBase :
    SourceTopologicalGroupMonoidActionPair.Iso
      zeroPair
      (symmetry.pair symmetry.baseLabel)

namespace SourceIUTIIZeroLabelConstantComparison

variable
  {l : PrimeGeFive}
  {symmetry :
    SourceIUTIISymmetrizingIsomorphisms.{u} l}
  (comparison :
    SourceIUTIIZeroLabelConstantComparison
      symmetry)

/-- The zero-to-label comparison obtained through the symmetrized base. -/
noncomputable def zeroToLabel
    (label : IUTIPositiveLabel.{u} l) :
    SourceTopologicalGroupMonoidActionPair.Iso
      comparison.zeroPair
      (symmetry.pair label) :=
  comparison.zeroToBase.trans
    (symmetry.fromBase label)

/--
The graph map from the zero-labeled constant monoid to all nonzero
symmetrized factors.
-/
noncomputable def zeroToDiagonalMonoidHom :
    comparison.zeroPair.monoidCarrier →*
      ∀ label,
        (symmetry.pair label).monoidCarrier :=
  Pi.monoidHom fun label =>
    (comparison.zeroToLabel
      label).monoidIso.toMulEquiv.toMonoidHom

theorem zeroToDiagonalMonoidHom_injective :
    Function.Injective
      comparison.zeroToDiagonalMonoidHom := by
  intro first second h
  have hBase :
      (comparison.zeroToLabel
          symmetry.baseLabel).monoidIso first =
        (comparison.zeroToLabel
          symmetry.baseLabel).monoidIso second :=
    by
      change
        comparison.zeroToDiagonalMonoidHom
            first symmetry.baseLabel =
          comparison.zeroToDiagonalMonoidHom
            second symmetry.baseLabel
      exact congrFun h symmetry.baseLabel
  exact
    (comparison.zeroToLabel
      symmetry.baseLabel).monoidIso.injective hBase

/-- The diagonal submonoid which is the graph of the zero-labeled factor. -/
noncomputable def zeroDiagonalSubmonoid :
    Submonoid
      (∀ label,
        (symmetry.pair label).monoidCarrier) :=
  MonoidHom.mrange
    comparison.zeroToDiagonalMonoidHom

/--
The zero-label graph map factors through the same diagonal embedding derived
from the nonzero-label symmetrizing isomorphisms.
-/
theorem zeroToDiagonalMonoidHom_eq_diagonalMonoidHom
    (monoidElement :
      comparison.zeroPair.monoidCarrier) :
    comparison.zeroToDiagonalMonoidHom monoidElement =
      symmetry.diagonalMonoidHom
        (comparison.zeroToBase.monoidIso monoidElement) := by
  funext label
  rfl

/--
The graph determined by the zero-labeled factor is exactly the diagonal range
from Corollary 3.5(i), not merely an isomorphic separately chosen submonoid.
-/
theorem zeroDiagonalSubmonoid_eq_diagonalRangeSubmonoid :
    comparison.zeroDiagonalSubmonoid =
      symmetry.diagonalRangeSubmonoid := by
  ext profile
  constructor
  · rintro ⟨monoidElement, rfl⟩
    refine
      ⟨comparison.zeroToBase.monoidIso
          monoidElement, ?_⟩
    exact
      comparison.zeroToDiagonalMonoidHom_eq_diagonalMonoidHom
        monoidElement
  · rintro ⟨monoidElement, rfl⟩
    refine
      ⟨comparison.zeroToBase.monoidIso.symm
          monoidElement, ?_⟩
    rw [
      comparison.zeroToDiagonalMonoidHom_eq_diagonalMonoidHom,
      comparison.zeroToBase.monoidIso.apply_symm_apply]

/--
The zero-labeled constant monoid is isomorphic to the symmetrized diagonal
submonoid, rather than being collapsed with the label set.
-/
noncomputable def zeroToDiagonalMulEquiv :
    comparison.zeroPair.monoidCarrier ≃*
      comparison.zeroDiagonalSubmonoid :=
  MulEquiv.ofBijective
    comparison.zeroToDiagonalMonoidHom.mrangeRestrict
    ⟨by
      intro first second h
      apply comparison.zeroToDiagonalMonoidHom_injective
      exact congrArg Subtype.val h,
    MonoidHom.mrangeRestrict_surjective
      comparison.zeroToDiagonalMonoidHom⟩

/-- The zero-label graph map is continuous in every nonzero label coordinate. -/
theorem continuous_zeroToDiagonalMonoidHom :
    Continuous comparison.zeroToDiagonalMonoidHom := by
  apply continuous_pi
  intro label
  exact
    (comparison.zeroToLabel label).monoidIso.continuous

/--
The zero-labeled constant monoid is continuously and multiplicatively
equivalent to its diagonal graph.
-/
noncomputable def zeroToDiagonalContinuousMulEquiv :
    comparison.zeroPair.monoidCarrier ≃ₜ*
      comparison.zeroDiagonalSubmonoid where
  toFun monoidElement :=
    ⟨comparison.zeroToDiagonalMonoidHom monoidElement,
      ⟨monoidElement, rfl⟩⟩
  invFun profile :=
    (comparison.zeroToLabel
      symmetry.baseLabel).monoidIso.symm
        (profile.1 symmetry.baseLabel)
  left_inv monoidElement := by
    change
      (comparison.zeroToLabel
          symmetry.baseLabel).monoidIso.symm
          ((comparison.zeroToDiagonalMonoidHom
            monoidElement) symmetry.baseLabel) =
        monoidElement
    exact
      (comparison.zeroToLabel
        symmetry.baseLabel).monoidIso.symm_apply_apply
          monoidElement
  right_inv profile := by
    rcases profile with
      ⟨_profile, ⟨monoidElement, rfl⟩⟩
    apply Subtype.ext
    change
      comparison.zeroToDiagonalMonoidHom
          ((comparison.zeroToLabel
              symmetry.baseLabel).monoidIso.symm
            ((comparison.zeroToDiagonalMonoidHom
              monoidElement) symmetry.baseLabel)) =
        comparison.zeroToDiagonalMonoidHom monoidElement
    apply congrArg
      comparison.zeroToDiagonalMonoidHom
    exact
      (comparison.zeroToLabel
        symmetry.baseLabel).monoidIso.symm_apply_apply
          monoidElement
  map_mul' first second := by
    apply Subtype.ext
    exact
      map_mul
        comparison.zeroToDiagonalMonoidHom
        first second
  continuous_toFun :=
    comparison.continuous_zeroToDiagonalMonoidHom.subtype_mk _
  continuous_invFun :=
    (comparison.zeroToLabel
        symmetry.baseLabel).monoidIso.symm.continuous.comp
      ((continuous_apply symmetry.baseLabel).comp
        continuous_subtype_val)

/--
The graph isomorphism is compatible with the zero action and each transported
labeled action.
-/
theorem zeroToDiagonalMonoidHom_equivariant
    (groupElement :
      comparison.zeroPair.actingGroup)
    (monoidElement :
      comparison.zeroPair.monoidCarrier) :
    comparison.zeroToDiagonalMonoidHom
        (comparison.zeroPair.action
          groupElement monoidElement) =
      fun label =>
        (symmetry.pair label).action
          ((comparison.zeroToLabel label).groupIso
            groupElement)
          (comparison.zeroToDiagonalMonoidHom
            monoidElement label) := by
  funext label
  change
    (comparison.zeroToLabel label).monoidIso
        (comparison.zeroPair.action
          groupElement monoidElement) =
      (symmetry.pair label).action
        ((comparison.zeroToLabel label).groupIso
          groupElement)
        ((comparison.zeroToLabel label).monoidIso
          monoidElement)
  exact
    (comparison.zeroToLabel label).equivariant
      groupElement monoidElement

end SourceIUTIIZeroLabelConstantComparison

end Iut
