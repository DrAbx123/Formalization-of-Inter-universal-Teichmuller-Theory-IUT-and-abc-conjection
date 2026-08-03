/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTheorem311

/-!
# Finite local Initial Theta groups as canonical MLF pairs

This module identifies the absolute-separable-closure Galois group stored by
the finite local Initial Theta core with the algebraic-closure model used by
MLF-Galois `TM`-pairs. The comparison is an actual topological group
isomorphism for the Krull topologies, not an input certificate.
-/

namespace Iut

universe u

open scoped Topology

namespace ProfiniteFundamentalExactSequence

variable {geometric arithmetic galois : ProfiniteGrp.{u}}
variable (sequence :
  ProfiniteFundamentalExactSequence geometric arithmetic galois)

/-- The arithmetic term of a profinite fundamental-group exact sequence as a
general topological group. -/
def arithmeticTopologicalGroup (arithmetic : ProfiniteGrp.{u}) :
    TopologicalGroupCat.{u} :=
  TopologicalGroupCat.ofProfinite arithmetic

/-- The full arithmetic group, used as the numerator of the local Galois
subquotient in IUT II, Definition 2.7(ii). -/
def arithmeticNumerator (arithmetic : ProfiniteGrp.{u}) :
    Subgroup (arithmeticTopologicalGroup arithmetic) :=
  ⊤

/-- The projection from the full arithmetic numerator to the Galois term. -/
def numeratorProjection :
    arithmeticNumerator arithmetic →ₜ* galois where
  toMonoidHom :=
    sequence.projection.hom.toMonoidHom.comp
      (arithmeticNumerator arithmetic).subtype
  continuous_toFun :=
    sequence.projection.hom.continuous_toFun.comp
      continuous_subtype_val

/-- Surjectivity of the numerator projection is inherited from exactness data. -/
theorem numeratorProjection_surjective :
    Function.Surjective sequence.numeratorProjection := by
  intro target
  obtain ⟨source, hsource⟩ := sequence.projection_surjective target
  exact ⟨⟨source, Subgroup.mem_top source⟩, hsource⟩

/-- The local Galois subquotient of the arithmetic fundamental group. -/
def localGaloisSubquotient :
    SourceTopologicalSubquotient
      (arithmeticTopologicalGroup arithmetic) where
  numerator := arithmeticNumerator arithmetic
  denominator := sequence.numeratorProjection.toMonoidHom.ker
  denominator_normal := by infer_instance

/-- Exactness identifies the quotient denominator with the geometric image. -/
theorem localGalois_denominator_eq_geometric_range_comap :
    sequence.localGaloisSubquotient.denominator =
      Subgroup.comap
        (arithmeticNumerator arithmetic).subtype
        sequence.inclusion.hom.toMonoidHom.range := by
  ext source
  change sequence.projection source.1 = 1 ↔
    source.1 ∈ sequence.inclusion.hom.toMonoidHom.range
  constructor
  · intro hsource
    rw [sequence.exact]
    exact hsource
  · intro hsource
    rw [sequence.exact] at hsource
    exact hsource

/-- The first-isomorphism-theorem equivalence from the local subquotient to
the Galois term. -/
noncomputable def localGaloisMulEquiv :
    sequence.localGaloisSubquotient.Carrier ≃* galois :=
  QuotientGroup.quotientKerEquivOfSurjective
    sequence.numeratorProjection.toMonoidHom
    sequence.numeratorProjection_surjective

/-- The forward local Galois quotient equivalence is continuous. -/
theorem continuous_localGaloisMulEquiv :
    Continuous sequence.localGaloisMulEquiv := by
  apply Continuous.quotient_lift
  exact sequence.numeratorProjection.continuous_toFun

/-- The full numerator inherits compactness from the profinite arithmetic
fundamental group. -/
noncomputable instance arithmeticNumeratorCompactSpace :
    CompactSpace (arithmeticNumerator arithmetic) := by
  change CompactSpace (⊤ : Subgroup arithmetic)
  exact isClosed_univ.isClosedEmbedding_subtypeVal.compactSpace

/-- The local Galois subquotient is compact. -/
noncomputable instance localGaloisSubquotientCompactSpace :
    CompactSpace sequence.localGaloisSubquotient.Carrier := by
  letI : CompactSpace sequence.localGaloisSubquotient.numerator := by
    change CompactSpace (arithmeticNumerator arithmetic)
    infer_instance
  exact Quotient.compactSpace

/-- The arithmetic quotient and the Galois term are topologically isomorphic.
Continuity of the inverse follows from compactness of the quotient and the
Hausdorff profinite topology on the Galois term. -/
noncomputable def localGaloisContinuousMulEquiv :
    sequence.localGaloisSubquotient.Carrier ≃ₜ* galois where
  toMulEquiv := sequence.localGaloisMulEquiv
  continuous_toFun := sequence.continuous_localGaloisMulEquiv
  continuous_invFun :=
    Continuous.continuous_symm_of_equiv_compact_to_t2
      sequence.continuous_localGaloisMulEquiv

/-- The topological quotient equivalence is induced by the original
arithmetic-to-Galois projection. -/
@[simp]
theorem localGaloisContinuousMulEquiv_projection
    (source : sequence.localGaloisSubquotient.numerator) :
    sequence.localGaloisContinuousMulEquiv
        (sequence.localGaloisSubquotient.projection source) =
      sequence.numeratorProjection source :=
  rfl

end ProfiniteFundamentalExactSequence

namespace SourceMLFGaloisComparison

/--
Conjugation across an algebra equivalence is continuous for the two Krull
topologies. A basic open stabilizer of a finite intermediate field pulls back
to the stabilizer of its inverse image, which is again finite.
-/
theorem continuous_autCongr
    {K L E : Type u}
    [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E]
    (equivalence : L ≃ₐ[K] E) :
    Continuous (AlgEquiv.autCongr equivalence) := by
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def]
  intro targetNeighborhood target_mem
  rw [map_one, krullTopology_mem_nhds_one_iff] at target_mem
  rcases target_mem with
    ⟨targetField, target_finite, target_fixing_le⟩
  let sourceField : IntermediateField K L :=
    targetField.map equivalence.symm.toAlgHom
  letI : FiniteDimensional K targetField := target_finite
  letI : FiniteDimensional K sourceField :=
    LinearEquiv.finiteDimensional
      (IntermediateField.equivMap
        targetField equivalence.symm.toAlgHom).toLinearEquiv
  apply mem_nhds_iff.mpr
  refine
    ⟨sourceField.fixingSubgroup,
      ?_, IntermediateField.fixingSubgroup_isOpen sourceField,
      one_mem _⟩
  intro sigma sigma_mem
  apply target_fixing_le
  apply (IntermediateField.mem_fixingSubgroup_iff targetField _).mpr
  intro value value_mem
  have source_value_mem :
      equivalence.symm (value : E) ∈ sourceField := by
    change equivalence.symm (value : E) ∈
      targetField.map equivalence.symm.toAlgHom
    exact ⟨value, value_mem, rfl⟩
  have sigma_fixes :=
    ((IntermediateField.mem_fixingSubgroup_iff sourceField _).mp sigma_mem)
      (equivalence.symm (value : E)) source_value_mem
  change
    equivalence
        (sigma (equivalence.symm (value : E))) =
      value
  rw [sigma_fixes]
  exact equivalence.apply_symm_apply value

/-- Galois transport across an algebra equivalence is a topological group equivalence. -/
noncomputable def continuousAutCongr
    {K L E : Type u}
    [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E]
    (equivalence : L ≃ₐ[K] E) :
    Gal(L/K) ≃ₜ* Gal(E/K) where
  toMulEquiv := AlgEquiv.autCongr equivalence
  continuous_toFun := continuous_autCongr equivalence
  continuous_invFun := by
    change Continuous (AlgEquiv.autCongr equivalence).symm
    rw [AlgEquiv.autCongr_symm]
    exact continuous_autCongr equivalence.symm

/-- In characteristic zero, the absolute separable closure is the algebraic closure. -/
noncomputable def separableClosureEquivAlgebraicClosure
    (K : Type u) [Field K] [CharZero K] :
    SeparableClosure K ≃ₐ[K] AlgebraicClosure K :=
  (IntermediateField.equivOfEq
      ((separableClosure.eq_top_iff
        (F := K) (E := AlgebraicClosure K)).mpr inferInstance)).trans
    IntermediateField.topEquiv

/-- The two standard characteristic-zero absolute Galois models agree topologically. -/
noncomputable def absoluteGaloisEquiv
    (K : Type u) [Field K] [CharZero K] :
    Gal(SeparableClosure K / K) ≃ₜ*
      Gal(AlgebraicClosure K / K) :=
  continuousAutCongr (separableClosureEquivAlgebraicClosure K)

end SourceMLFGaloisComparison

namespace SourceMLFGaloisTMPair

/-- The canonical MLF pair on the separable-closure absolute Galois model. -/
noncomputable def monoAnalyticSeparable
    (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [CharZero K] :
    SourceMLFGaloisTMPair
      (TopologicalGroupCat.ofProfinite (AbsoluteGaloisProfinite K)) := by
  let comparison := SourceMLFGaloisComparison.absoluteGaloisEquiv K
  let modelPair := SourceMLFGaloisTMPair.monoAnalytic K
  exact
    { arithmeticMonoid := modelPair.arithmeticMonoid
      action := modelPair.action.comp comparison.toMonoidHom
      modelField := K
      modelFieldStructure := inferInstance
      modelValuativeRel := inferInstance
      modelTopology := inferInstance
      modelIsMLF := inferInstance
      modelCharZero := inferInstance
      model := modelPair.model
      groupIso := comparison.symm
      monoidIso := MulEquiv.refl _
      equivariant := by
        intro modelGroupElement modelMonoidElement
        change
          modelPair.action modelGroupElement modelMonoidElement =
            modelPair.action
              (comparison (comparison.symm modelGroupElement))
              modelMonoidElement
        rw [comparison.apply_symm_apply] }

/-- Pull an MLF-Galois pair back across an isomorphism of acting groups. -/
noncomputable def pullbackActingGroup
    {G H : TopologicalGroupCat.{u}}
    (pair : SourceMLFGaloisTMPair H)
    (equivalence : G ≃ₜ* H) :
    SourceMLFGaloisTMPair G where
  arithmeticMonoid := pair.arithmeticMonoid
  action := pair.action.comp equivalence.toMonoidHom
  modelField := pair.modelField
  modelFieldStructure := pair.modelFieldStructure
  modelValuativeRel := pair.modelValuativeRel
  modelTopology := pair.modelTopology
  modelIsMLF := pair.modelIsMLF
  modelCharZero := pair.modelCharZero
  model := pair.model
  groupIso := pair.groupIso.trans equivalence.symm
  monoidIso := pair.monoidIso
  equivariant := by
    intro modelGroupElement modelMonoidElement
    change
      pair.monoidIso
          (pair.model.action modelGroupElement modelMonoidElement) =
        pair.action
          (equivalence
            (equivalence.symm
              (pair.groupIso modelGroupElement)))
          (pair.monoidIso modelMonoidElement)
    rw [equivalence.apply_symm_apply]
    exact pair.equivariant modelGroupElement modelMonoidElement

@[simp]
theorem pullbackActingGroup_action
    {G H : TopologicalGroupCat.{u}}
    (pair : SourceMLFGaloisTMPair H)
    (equivalence : G ≃ₜ* H)
    (groupElement : G)
    (monoidElement : pair.arithmeticMonoid.carrier) :
    (pair.pullbackActingGroup equivalence).action
        groupElement monoidElement =
      pair.action (equivalence groupElement) monoidElement :=
  rfl

end SourceMLFGaloisTMPair

noncomputable instance ThetaFinitePlace.completionValuativeRel
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    ValuativeRel (ThetaFinitePlace.Completion v) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (ThetaFinitePlace.Completion v)
      (WithZero (Multiplicative ℤ)))

noncomputable instance ThetaFinitePlace.completionValuationCompatible
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    (Valued.v : Valuation (ThetaFinitePlace.Completion v)
      (WithZero (Multiplicative ℤ))).Compatible :=
  Valuation.Compatible.ofValuation _

noncomputable instance ThetaFinitePlace.completionIsValuativeTopology
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    IsValuativeTopology (ThetaFinitePlace.Completion v) :=
  IsValuativeTopology.of_zero fun neighborhood => by
    rw [Valued.mem_nhds_zero]
    simpa using
      ((Valued.v : Valuation (ThetaFinitePlace.Completion v)
        (WithZero (Multiplicative ℤ))).exists_setOf_restrict_le_iff
          (0 : ThetaFinitePlace.Completion v) neighborhood)

noncomputable instance ThetaFinitePlace.completionIsNonarchimedeanLocalField
    {K : Type u} [Field K] [NumberField K]
    (v : NumberField.FinitePlace K) :
    IsNonarchimedeanLocalField (ThetaFinitePlace.Completion v) where
  toIsValuativeTopology := inferInstance
  toLocallyCompactSpace := inferInstance
  toIsNontrivial :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v : Valuation (ThetaFinitePlace.Completion v)
        (WithZero (Multiplicative ℤ)))).mpr inferInstance

namespace SourceThetaFiniteLocalCoreData

variable
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.FinitePlace K}

/-- The canonical MLF pair on the exact local Galois group of an Initial Theta core. -/
noncomputable def mlfGaloisTMPair
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :
    SourceMLFGaloisTMPair
      (TopologicalGroupCat.ofProfinite core.orbicurves.absoluteGalois) :=
  SourceMLFGaloisTMPair.monoAnalyticSeparable
    (ThetaFinitePlace.Completion v)

/-- The coefficient-identity unit Kummer embedding on the local Initial Theta group. -/
noncomputable def unitKummerEmbedding
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :=
  SourceIUTIIUnitKummerEmbedding.canonical core.mlfGaloisTMPair

/-- The constructed local Initial Theta unit Kummer map is faithful. -/
theorem unitKummer_injective
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :
    Function.Injective core.unitKummerEmbedding.unitKummer :=
  SourceIUTIIUnitKummerEmbedding.canonical_unitKummer_injective
    core.mlfGaloisTMPair

/-- The local-Galois subquotient of the arithmetic `X_v` fundamental group. -/
noncomputable def xLocalGaloisSubquotient
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :=
  core.orbicurves.xFundamentalGroups.exactSequence.localGaloisSubquotient

/-- The exact-sequence quotient is the stored local absolute Galois group. -/
noncomputable def xLocalGaloisContinuousMulEquiv
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :
    core.xLocalGaloisSubquotient.toTopologicalGroupCat ≃ₜ*
      TopologicalGroupCat.ofProfinite core.orbicurves.absoluteGalois :=
  core.orbicurves.xFundamentalGroups.exactSequence.localGaloisContinuousMulEquiv

/-- The canonical MLF pair transported to the actual `X_v` local-Galois
subquotient of IUT II, Definition 2.7(ii). -/
noncomputable def xLocalGaloisTMPair
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :
    SourceMLFGaloisTMPair
      core.xLocalGaloisSubquotient.toTopologicalGroupCat :=
  core.mlfGaloisTMPair.pullbackActingGroup
    core.xLocalGaloisContinuousMulEquiv

@[simp]
theorem xLocalGaloisTMPair_action
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v)
    (groupElement : core.xLocalGaloisSubquotient.Carrier)
    (monoidElement : core.mlfGaloisTMPair.arithmeticMonoid.carrier) :
    core.xLocalGaloisTMPair.action groupElement monoidElement =
      core.mlfGaloisTMPair.action
        (core.xLocalGaloisContinuousMulEquiv groupElement)
        monoidElement :=
  rfl

/-- The canonical cyclotomic coefficient action pulled back from `G_v` to its
exact-sequence quotient. -/
noncomputable def xLocalGaloisCoefficientAction
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :=
  core.mlfGaloisTMPair.continuousCyclotomeAction.comap
    (ContinuousMonoidHom.toContinuousMonoidHom
      core.xLocalGaloisContinuousMulEquiv)

@[simp]
theorem xLocalGaloisCoefficientAction_act
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v)
    (groupElement : core.xLocalGaloisSubquotient.Carrier)
    (coefficient :
      SourceMonoidCyclotome
        core.mlfGaloisTMPair.arithmeticMonoid.carrier) :
    core.xLocalGaloisCoefficientAction.act groupElement coefficient =
      core.mlfGaloisTMPair.continuousCyclotomeAction.act
        (core.xLocalGaloisContinuousMulEquiv groupElement)
        coefficient :=
  rfl

/-- Cohomological restriction from the stored `G_v` to its isomorphic
arithmetic-group quotient. This supplies the local-Galois endpoint comparison
needed before the two restrictions of IUT II, Corollary 2.8(i). -/
noncomputable def xLocalGaloisH1Restriction
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :
    ContinuousH1Germ
        core.mlfGaloisTMPair.continuousCyclotomeAction →*
      ContinuousH1Germ core.xLocalGaloisCoefficientAction :=
  ContinuousH1Germ.restrictMonoidHom
    (ContinuousMonoidHom.toContinuousMonoidHom
      core.xLocalGaloisContinuousMulEquiv)

/-- The local monoid Kummer map induced by cohomological restriction. -/
noncomputable def xLocalGaloisRestrictedMonoidKummer
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :
    core.mlfGaloisTMPair.arithmeticMonoid.carrier →*
      ContinuousH1Germ core.xLocalGaloisCoefficientAction :=
  core.xLocalGaloisH1Restriction.comp
    core.unitKummerEmbedding.monoidKummer

/-- The monoid Kummer/restriction square commutes. -/
theorem xLocalGaloisRestrictedMonoidKummer_commutes
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v)
    (value : core.mlfGaloisTMPair.arithmeticMonoid.carrier) :
    core.xLocalGaloisRestrictedMonoidKummer value =
      core.xLocalGaloisH1Restriction
        (core.unitKummerEmbedding.monoidKummer value) :=
  rfl

/-- The local unit Kummer map induced by the same cohomological restriction. -/
noncomputable def xLocalGaloisRestrictedUnitKummer
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :
    core.mlfGaloisTMPair.arithmeticMonoid.carrierˣ →*
      ContinuousH1Germ core.xLocalGaloisCoefficientAction :=
  core.xLocalGaloisH1Restriction.comp
    core.unitKummerEmbedding.unitKummer

/-- The unit Kummer/restriction square commutes. -/
theorem xLocalGaloisRestrictedUnitKummer_commutes
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v)
    (value : core.mlfGaloisTMPair.arithmeticMonoid.carrierˣ) :
    core.xLocalGaloisRestrictedUnitKummer value =
      core.xLocalGaloisH1Restriction
        (core.unitKummerEmbedding.unitKummer value) :=
  rfl

/-- The canonical unit Kummer embedding on the literal local-Galois quotient. -/
noncomputable def xLocalGaloisUnitKummerEmbedding
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :=
  SourceIUTIIUnitKummerEmbedding.canonical core.xLocalGaloisTMPair

/-- Compactness of the literal local-Galois quotient. -/
noncomputable instance xLocalGaloisCompactSpace
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :
    CompactSpace
      core.xLocalGaloisSubquotient.toTopologicalGroupCat := by
  change CompactSpace core.xLocalGaloisSubquotient.Carrier
  change CompactSpace
    core.orbicurves.xFundamentalGroups.exactSequence.localGaloisSubquotient.Carrier
  infer_instance

/-- The quotient-local canonical unit Kummer map is faithful. -/
theorem xLocalGaloisUnitKummer_injective
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v) :
    Function.Injective core.xLocalGaloisUnitKummerEmbedding.unitKummer :=
  SourceIUTIIUnitKummerEmbedding.canonical_unitKummer_injective
    core.xLocalGaloisTMPair

end SourceThetaFiniteLocalCoreData

end Iut
