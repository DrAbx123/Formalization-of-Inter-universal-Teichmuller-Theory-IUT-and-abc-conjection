/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceMLFIntegralMonoid
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.Countable
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace

open CategoryTheory

namespace Iut

universe u

namespace ThetaFinitePlace

variable {K : Type u} [Field K] [NumberField K]

noncomputable abbrev underlyingPrime
    (place : NumberField.FinitePlace K) :=
  LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime place

noncomputable abbrev comap
    {k : Type*} [Field k] [NumberField k] [Algebra k K]
    (place : NumberField.FinitePlace K) :
    NumberField.FinitePlace k :=
  LeanFormal.IUT.NumberFieldFinitePlace.comap (k := k) place

noncomputable abbrev Completion
    (place : NumberField.FinitePlace K) :=
  LeanFormal.IUT.NumberFieldFinitePlace.Completion place

noncomputable def completionRingHom
    (place : NumberField.FinitePlace K) :
    Completion (comap (k := ℚ) place) →+* Completion place :=
  LeanFormal.IUT.NumberFieldFinitePlace.completionMap (k := ℚ) place

theorem continuous_completionRingHom
    (place : NumberField.FinitePlace K) :
    Continuous (completionRingHom place) :=
  LeanFormal.IUT.NumberFieldFinitePlace.continuous_completionMap
    (k := ℚ) place

theorem completionRingHom_ratCast
    (place : NumberField.FinitePlace K) (scalar : ℚ) :
    completionRingHom place
        (scalar : Completion (comap (k := ℚ) place)) =
      (scalar : Completion place) := by
  exact map_ratCast (completionRingHom place) scalar

noncomputable instance completionAlgebra
    (place : NumberField.FinitePlace K) :
    Algebra (Completion (comap (k := ℚ) place)) (Completion place) :=
  (completionRingHom place).toAlgebra

noncomputable instance completionContinuousSMul
    (place : NumberField.FinitePlace K) :
    ContinuousSMul (Completion (comap (k := ℚ) place)) (Completion place) :=
  continuousSMul_of_algebraMap _ _ (continuous_completionRingHom place)

noncomputable instance completionScalarTower
    (place : NumberField.FinitePlace K) :
    IsScalarTower ℚ (Completion (comap (k := ℚ) place))
      (Completion place) := by
  letI : Algebra ℚ (Completion (comap (k := ℚ) place)) :=
    IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
      (NumberField.RingOfIntegers ℚ) ℚ
      (underlyingPrime (comap (k := ℚ) place))
  letI : Algebra ℚ (Completion place) :=
    IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
      (NumberField.RingOfIntegers K) K (underlyingPrime place)
  apply IsScalarTower.of_algebraMap_eq
    (R := ℚ) (S := Completion (comap (k := ℚ) place))
    (A := Completion place)
  intro scalar
  have htarget : algebraMap ℚ (Completion place) scalar =
      (scalar : Completion place) := by
    simp
  have hbase : algebraMap ℚ (Completion (comap (k := ℚ) place)) scalar =
      (scalar : Completion (comap (k := ℚ) place)) := by
    simp
  rw [htarget, hbase]
  exact (completionRingHom_ratCast place scalar).symm

noncomputable instance finiteDimensional
    (place : NumberField.FinitePlace K) :
    FiniteDimensional
      (Completion (comap (k := ℚ) place))
      (Completion place) := by
  letI : Module.Finite
      (Completion (comap (k := ℚ) place))
      (Completion place) :=
    NumberField.HeightOneSpectrum.instFiniteAdicCompletionRingOfIntegers
      (underlyingPrime (comap (k := ℚ) place))
      (underlyingPrime place)
  infer_instance

noncomputable instance completionNontriviallyNormedField
    (place : NumberField.FinitePlace K) :
    NontriviallyNormedField (Completion place) :=
  NontriviallyNormedField.ofNormNeOne <| by
    let prime := underlyingPrime place
    obtain ⟨uniformizer, huniformizer⟩ :=
      prime.valuation_exists_uniformizer K
    have hne : uniformizer ≠ 0 := by
      apply (prime.valuation K).ne_zero_iff.mp
      rw [huniformizer]
      simp
    refine ⟨NumberField.FinitePlace.embedding prime uniformizer,
      (map_ne_zero (NumberField.FinitePlace.embedding prime)).mpr hne, ?_⟩
    rw [NumberField.FinitePlace.norm_embedding', huniformizer]
    norm_cast
    rw [WithZeroMulInt.toNNReal_eq_one_iff _
      (NumberField.HeightOneSpectrum.absNorm_ne_zero prime)
      (ne_of_gt (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal prime))]
    simp

noncomputable instance completionCharZero
    (place : NumberField.FinitePlace K) :
    CharZero (Completion place) :=
  charZero_of_injective_algebraMap
    (RingHom.injective (algebraMap ℚ (Completion place)))

noncomputable instance completionValuativeRel
    (place : NumberField.FinitePlace K) :
    ValuativeRel (Completion place) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (Completion place)
      (WithZero (Multiplicative ℤ)))

noncomputable instance completionSecondCountableTopology
    (place : NumberField.FinitePlace K) :
    SecondCountableTopology (Completion place) := by
  letI : Countable K :=
    Finsupp.Countable.of_moduleFinite (R := ℚ) (M := K)
  letI : TopologicalSpace.SeparableSpace (Completion place) :=
    TopologicalSpace.SeparableSpace.of_denseRange
      (algebraMap K (Completion place))
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
        K (underlyingPrime place))
  exact UniformSpace.secondCountable_of_separable (Completion place)

noncomputable instance rationalCompletionLocallyCompactSpace
    (place : NumberField.FinitePlace ℚ) :
    LocallyCompactSpace (Completion place) := by
  letI : Algebra ℚ (Completion place) :=
    IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
      (NumberField.RingOfIntegers ℚ) ℚ (underlyingPrime place)
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
    (underlyingPrime place)).toHomeomorph
      |>.locallyCompactSpace_iff.mpr inferInstance

end ThetaFinitePlace

structure SourceFiniteIndTopologicalLocalModule
    (rationalPlace : NumberField.FinitePlace ℚ) where
  stageIndex : Type u
  [stageCategory : SmallCategory stageIndex]
  [stageFiltered : IsFiltered stageIndex]
  stageDiagram :
    CategoryTheory.Cat.of stageIndex ⥤
      TopModuleCat.{u} (ThetaFinitePlace.Completion rationalPlace)
  stage_finiteDimensional :
    ∀ stage,
      FiniteDimensional (ThetaFinitePlace.Completion rationalPlace)
        (stageDiagram.obj stage)
  colimitCocone : Limits.Cocone stageDiagram
  colimitIsColimit : Limits.IsColimit colimitCocone

attribute [instance]
  SourceFiniteIndTopologicalLocalModule.stageCategory
  SourceFiniteIndTopologicalLocalModule.stageFiltered
  SourceFiniteIndTopologicalLocalModule.stage_finiteDimensional

namespace SourceFiniteIndTopologicalLocalModule

noncomputable abbrev carrier
    {rationalPlace : NumberField.FinitePlace ℚ}
    (module : SourceFiniteIndTopologicalLocalModule.{u} rationalPlace) :=
  module.colimitCocone.pt

end SourceFiniteIndTopologicalLocalModule

end Iut
