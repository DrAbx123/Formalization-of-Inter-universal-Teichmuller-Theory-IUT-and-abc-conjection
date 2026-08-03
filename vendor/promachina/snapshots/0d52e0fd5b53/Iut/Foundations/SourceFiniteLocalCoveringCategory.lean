/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceConnectedCoveringQuotient
import Iut.Foundations.SourceInitialThetaData

/-!
# Finite-local connected covering categories

This file constructs the good finite-place categories in IUT I, Example 3.3.
For an exact sequence `1 → Δ → Π → G → 1`, the local covering
category is `B(Π)⁰` and the base-field boundary is `B(G)⁰`.  Pullback
along `Π → G` is fully faithful; taking `Δ`-orbits is its left adjoint.

At a good selected place these groups are not new inputs: they are the
arithmetic and Galois terms of the exact sequence already certified by the
finite-local `X`-orbicurve.  The equivalence with its stored finite-etale cover
category is retained as the Galois semantics of the construction.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace ProfiniteFundamentalExactSequence

variable {geometric arithmetic galois : ProfiniteGrp.{u}}
variable (sequence :
  ProfiniteFundamentalExactSequence geometric arithmetic galois)

/-- Connected covers classified by the arithmetic fundamental group. -/
abbrev connectedArithmeticCoveringCategory
    (_sequence :
      ProfiniteFundamentalExactSequence geometric arithmetic galois) :=
  SourceConnectedCoveringCategory arithmetic

/-- Connected covers classified by the base-field Galois group. -/
abbrev connectedBaseCoveringCategory
    (_sequence :
      ProfiniteFundamentalExactSequence geometric arithmetic galois) :=
  SourceConnectedCoveringCategory galois

/-- Pullback of a connected base-field cover along the arithmetic-to-Galois
projection. -/
noncomputable def connectedBaseEmbedding :
    sequence.connectedBaseCoveringCategory ⥤
      sequence.connectedArithmeticCoveringCategory :=
  SourceActionKernelQuotient.connectedRestriction
    sequence.projection sequence.projection_surjective

/-- The base-field hull of a connected arithmetic cover, obtained by dividing
its fiber by the geometric kernel. -/
noncomputable def connectedBaseHull :
    sequence.connectedArithmeticCoveringCategory ⥤
      sequence.connectedBaseCoveringCategory :=
  SourceActionKernelQuotient.connectedFunctor
    sequence.projection sequence.projection_surjective

/-- The base-field hull is left adjoint to pullback from the base field. -/
noncomputable def connectedBaseHullAdjunction :
    sequence.connectedBaseHull ⊣ sequence.connectedBaseEmbedding :=
  SourceActionKernelQuotient.connectedAdjunction
    sequence.projection sequence.projection_surjective

/-- Pullback from the base field is fully faithful. -/
noncomputable def connectedBaseEmbeddingFullyFaithful :
    sequence.connectedBaseEmbedding.FullyFaithful := by
  change
    (SourceActionKernelQuotient.connectedRestriction
      sequence.projection sequence.projection_surjective).FullyFaithful
  letI := SourceActionKernelQuotient.connectedRestrictionFull
    sequence.projection sequence.projection_surjective
  letI := SourceActionKernelQuotient.connectedRestrictionFaithful
    sequence.projection sequence.projection_surjective
  exact Functor.FullyFaithful.ofFullyFaithful _

end ProfiniteFundamentalExactSequence

namespace SourceThetaFiniteLocalCoreData

variable
    {K : Type u} [Field K] [NumberField K]
    {curve : PuncturedEllipticCurve K}
    {kOrbicurves : SignQuotientOrbicurveData K curve}
    {v : NumberField.FinitePlace K}
    (core : SourceThetaFiniteLocalCoreData K curve kOrbicurves v)

/-- The certified arithmetic exact sequence of the local `X`-orbicurve. -/
noncomputable abbrev xLocalExactSequence :=
  core.orbicurves.xFundamentalGroups.exactSequence

/-- `D_v` at a good finite place: connected finite continuous actions of the
actual local arithmetic fundamental group. -/
abbrev connectedFiniteEtaleCoveringCategory :=
  core.xLocalExactSequence.connectedArithmeticCoveringCategory

/-- `D_v^⊢` at a good finite place: connected finite continuous actions of
the actual local absolute Galois group. -/
abbrev connectedBaseFieldCoveringCategory :=
  core.xLocalExactSequence.connectedBaseCoveringCategory

/-- The stored finite-etale cover category of the local `X`-orbicurve has the
continuous-action semantics used to define `D_v`. -/
noncomputable def xCoverActionEquivalence :
    let arithmetic :=
      core.orbicurves.xFundamentalGroups.arithmetic.toEtaleFundamentalGroup
    letI := arithmetic.coverCategory
    arithmetic.Cover ≌
      ContAction FintypeCat.{u}
        core.orbicurves.xFundamentalGroups.arithmetic.group :=
  EtaleFundamentalGroup.coverActionEquivalence
    core.orbicurves.xFundamentalGroups.arithmetic.toEtaleFundamentalGroup

/-- The source full embedding `D_v^⊢ ⟶ D_v`. -/
noncomputable def connectedBaseFieldEmbedding :
    core.connectedBaseFieldCoveringCategory ⥤
      core.connectedFiniteEtaleCoveringCategory :=
  core.xLocalExactSequence.connectedBaseEmbedding

/-- The source left adjoint `D_v ⟶ D_v^⊢`. -/
noncomputable def connectedBaseFieldHull :
    core.connectedFiniteEtaleCoveringCategory ⥤
      core.connectedBaseFieldCoveringCategory :=
  core.xLocalExactSequence.connectedBaseHull

/-- The local hull/pullback adjunction. -/
noncomputable def connectedBaseFieldAdjunction :
    core.connectedBaseFieldHull ⊣
      core.connectedBaseFieldEmbedding :=
  core.xLocalExactSequence.connectedBaseHullAdjunction

/-- The local base-field embedding is fully faithful. -/
noncomputable def connectedBaseFieldEmbeddingFullyFaithful :
    core.connectedBaseFieldEmbedding.FullyFaithful :=
  core.xLocalExactSequence.connectedBaseEmbeddingFullyFaithful

end SourceThetaFiniteLocalCoreData

namespace SourceInitialThetaCore

variable
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : SourceInitialThetaCore Fmod F K)
    (v : NumberField.FinitePlace K)
    (hv : v ∈ theta.valuations.good)

/-- The selected good-place category `D_v`, derived from `theta` rather than
accepted from the caller.  The proof records the source good-place branch. -/
abbrev goodFiniteLocalCoveringCategory
    (_hv : v ∈ theta.valuations.good) :=
  (theta.finiteLocalCores v).connectedFiniteEtaleCoveringCategory

/-- The reconstructed good-place base-field boundary `D_v^⊢`. -/
abbrev goodFiniteBaseFieldCoveringCategory
    (_hv : v ∈ theta.valuations.good) :=
  (theta.finiteLocalCores v).connectedBaseFieldCoveringCategory

/-- The source full embedding `D_v^⊢ ⟶ D_v` at a selected good place. -/
noncomputable def goodFiniteBaseFieldEmbedding :
    theta.goodFiniteBaseFieldCoveringCategory v hv ⥤
      theta.goodFiniteLocalCoveringCategory v hv :=
  (theta.finiteLocalCores v).connectedBaseFieldEmbedding

/-- The source left adjoint `D_v ⟶ D_v^⊢` at a selected good place. -/
noncomputable def goodFiniteBaseFieldHull :
    theta.goodFiniteLocalCoveringCategory v hv ⥤
      theta.goodFiniteBaseFieldCoveringCategory v hv :=
  (theta.finiteLocalCores v).connectedBaseFieldHull

/-- The selected good-place hull/pullback adjunction. -/
noncomputable def goodFiniteBaseFieldAdjunction :
    theta.goodFiniteBaseFieldHull v hv ⊣
      theta.goodFiniteBaseFieldEmbedding v hv :=
  (theta.finiteLocalCores v).connectedBaseFieldAdjunction

/-- The selected good-place base-field embedding is fully faithful. -/
noncomputable def goodFiniteBaseFieldEmbeddingFullyFaithful :
    (theta.goodFiniteBaseFieldEmbedding v hv).FullyFaithful :=
  (theta.finiteLocalCores v).connectedBaseFieldEmbeddingFullyFaithful

end SourceInitialThetaCore

end Iut
