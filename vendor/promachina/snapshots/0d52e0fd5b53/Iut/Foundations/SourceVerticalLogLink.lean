/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTheorem311

/-!
# Source vertical log-links for IUT III

This module formalizes the local content of IUT III, Definition 1.1 and the
adjacent correspondences used in Proposition 3.5(ii)(a)-(b).  A full log-link
is not an arbitrary relation between packet elements.  At a selected place it
consists of a topological field identification after the tautological local
logarithm, together with the realization of the adjacent target's local units
inside that field.  The one-step relation is then equality in the target field.

The relation is partial: a logarithm may fail to be a unit in the adjacent
target, exactly as in Remark 1.1.1.  No existence or totality statement is
inserted.  Proposition 3.5's tensor relations are derived componentwise from
these local full log-links below.
-/

namespace Iut

universe u

namespace SourceMonoAnalyticLogShellAlgorithm

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

/-- The selected-place field realization, transported along the equation
`v | v_Q`. -/
noncomputable def carrierAddEquivAbove
    (algorithm : SourceMonoAnalyticLogShellAlgorithm models)
    (strip : SourceDMonoAnalyticPrimeStrip models)
    (rationalPlace : SourceRationalPlace)
    (place : SourceSelectedPlaceAbove theta rationalPlace) :
    (algorithm.moduleAbove strip rationalPlace place).rationalCarrier ≃+
      SourceSelectedPlace.LogFieldCarrier place.1 := by
  rcases place with ⟨place, rfl⟩
  exact (algorithm.shell strip place).fieldRealization.carrierEquiv.toAddEquiv

end SourceMonoAnalyticLogShellAlgorithm

/--
One selected-place full log-link from a mono-analytic source strip to its
adjacent target.

At a finite place, the source invariant unit is sent through its actual
`p`-adic logarithm.  At an infinite place, it is sent through the source
principal logarithm.  The post-composition identifies the logarithmic field
with the target field.  The target-unit embeddings say what it means for the
result to lie again in the unit domain of the next log-link.
-/
structure SourceSelectedLocalFullLogLink
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
    (algorithm : SourceMonoAnalyticLogShellAlgorithm models)
    (source target : SourceDMonoAnalyticPrimeStrip models)
    (rationalPlace : SourceRationalPlace)
    (place : SourceSelectedPlaceAbove theta rationalPlace) where
  postcomposition :
    (algorithm.moduleAbove source rationalPlace place).rationalCarrier ≃L[ℚ]
      (algorithm.moduleAbove target rationalPlace place).rationalCarrier
  fieldPostcomposition :
    SourceSelectedPlace.LogFieldCarrier place.1 ≃+*
      SourceSelectedPlace.LogFieldCarrier place.1
  postcomposition_realization :
    ∀ value,
      algorithm.carrierAddEquivAbove target rationalPlace place
          (postcomposition value) =
        fieldPostcomposition
          (algorithm.carrierAddEquivAbove source rationalPlace place value)
  nonarchimedeanTargetUnitEmbedding :
    ∀ hkind : rationalPlace.kind = .nonarchimedean,
      ((algorithm.sourceDefinitionAbove target rationalPlace place
        ).asNonarchimedean hkind).localUnitData.localUnits →*
        (SourceSelectedPlace.LogFieldCarrier place.1)ˣ
  nonarchimedeanTargetUnitEmbedding_injective :
    ∀ hkind,
      Function.Injective (nonarchimedeanTargetUnitEmbedding hkind)
  nonarchimedeanTargetUnitRealization :
    ∀ hkind : rationalPlace.kind = .nonarchimedean,
      ((algorithm.sourceDefinitionAbove target rationalPlace place
        ).asNonarchimedean hkind).localUnitData.localUnits →
        (algorithm.moduleAbove target rationalPlace place).rationalCarrier
  nonarchimedeanTargetUnitRealization_continuous :
    ∀ hkind, Continuous (nonarchimedeanTargetUnitRealization hkind)
  nonarchimedeanTargetUnitRealization_field :
    ∀ hkind unit,
      algorithm.carrierAddEquivAbove target rationalPlace place
          (nonarchimedeanTargetUnitRealization hkind unit) =
        (nonarchimedeanTargetUnitEmbedding hkind unit :
          SourceSelectedPlace.LogFieldCarrier place.1)
  archimedeanTargetUnitEmbedding :
    ∀ _hkind : rationalPlace.kind = .archimedean,
      Circle →* (SourceSelectedPlace.LogFieldCarrier place.1)ˣ
  archimedeanTargetUnitEmbedding_injective :
    ∀ hkind,
      Function.Injective (archimedeanTargetUnitEmbedding hkind)
  archimedeanTargetUnitRealization :
    ∀ _hkind : rationalPlace.kind = .archimedean,
      Circle →
        (algorithm.moduleAbove target rationalPlace place).rationalCarrier
  archimedeanTargetUnitRealization_continuous :
    ∀ hkind, Continuous (archimedeanTargetUnitRealization hkind)
  archimedeanTargetUnitRealization_field :
    ∀ hkind unit,
      algorithm.carrierAddEquivAbove target rationalPlace place
          (archimedeanTargetUnitRealization hkind unit) =
        (archimedeanTargetUnitEmbedding hkind unit :
          SourceSelectedPlace.LogFieldCarrier place.1)

namespace SourceSelectedLocalFullLogLink

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
    {algorithm : SourceMonoAnalyticLogShellAlgorithm models}
    {source target : SourceDMonoAnalyticPrimeStrip models}
    {rationalPlace : SourceRationalPlace}
    {place : SourceSelectedPlaceAbove theta rationalPlace}

/-- Definition 1.1(i): the source `p`-adic logarithm is a target local unit. -/
noncomputable def NonarchimedeanRelated
    (link : SourceSelectedLocalFullLogLink algorithm source target
      rationalPlace place)
    (hkind : rationalPlace.kind = .nonarchimedean)
    (sourceUnit :
      ((algorithm.sourceDefinitionAbove source rationalPlace place).asNonarchimedean
        hkind).invariantLocalUnits)
    (targetUnit :
      ((algorithm.sourceDefinitionAbove target rationalPlace place).asNonarchimedean
        hkind).invariantLocalUnits) : Prop :=
  link.postcomposition
      (((algorithm.sourceDefinitionAbove source rationalPlace place).asNonarchimedean
        hkind).padicLog sourceUnit).toAdd =
    link.nonarchimedeanTargetUnitRealization hkind targetUnit.1

/-- Definition 1.1(ii): the source principal logarithm is a target circle unit. -/
noncomputable def ArchimedeanRelated
    (link : SourceSelectedLocalFullLogLink algorithm source target
      rationalPlace place)
    (hkind : rationalPlace.kind = .archimedean)
    (sourceUnit targetUnit : SourceAutHolomorphicSemiGerm.unitCircle) : Prop :=
  link.postcomposition
      (((algorithm.sourceDefinitionAbove source rationalPlace place).asArchimedean
        hkind).principalLog
          (SourceAutHolomorphicSemiGerm.circleEquivUnitCore.symm
            sourceUnit)) =
    link.archimedeanTargetUnitRealization hkind
      (SourceAutHolomorphicSemiGerm.circleEquivUnitCore.symm targetUnit)

/-- A finite full log-link has at most one adjacent target unit. -/
theorem nonarchimedean_target_unique
    (link : SourceSelectedLocalFullLogLink algorithm source target
      rationalPlace place)
    (hkind : rationalPlace.kind = .nonarchimedean)
    (sourceUnit :
      ((algorithm.sourceDefinitionAbove source rationalPlace place).asNonarchimedean
        hkind).invariantLocalUnits)
    {first second :
      ((algorithm.sourceDefinitionAbove target rationalPlace place).asNonarchimedean
        hkind).invariantLocalUnits}
    (hfirst : link.NonarchimedeanRelated hkind sourceUnit first)
    (hsecond : link.NonarchimedeanRelated hkind sourceUnit second) :
    first = second := by
  apply Subtype.ext
  apply link.nonarchimedeanTargetUnitEmbedding_injective hkind
  apply Units.ext
  calc
    (link.nonarchimedeanTargetUnitEmbedding hkind first.1 :
        SourceSelectedPlace.LogFieldCarrier place.1) =
        algorithm.carrierAddEquivAbove target rationalPlace place
          (link.nonarchimedeanTargetUnitRealization hkind first.1) :=
      (link.nonarchimedeanTargetUnitRealization_field hkind first.1).symm
    _ = algorithm.carrierAddEquivAbove target rationalPlace place
          (link.nonarchimedeanTargetUnitRealization hkind second.1) :=
      congrArg (algorithm.carrierAddEquivAbove target rationalPlace place)
        (hfirst.symm.trans hsecond)
    _ = (link.nonarchimedeanTargetUnitEmbedding hkind second.1 :
        SourceSelectedPlace.LogFieldCarrier place.1) :=
      link.nonarchimedeanTargetUnitRealization_field hkind second.1

/-- An archimedean full log-link has at most one adjacent target circle unit. -/
theorem archimedean_target_unique
    (link : SourceSelectedLocalFullLogLink algorithm source target
      rationalPlace place)
    (hkind : rationalPlace.kind = .archimedean)
    (sourceUnit : SourceAutHolomorphicSemiGerm.unitCircle)
    {first second : SourceAutHolomorphicSemiGerm.unitCircle}
    (hfirst : link.ArchimedeanRelated hkind sourceUnit first)
    (hsecond : link.ArchimedeanRelated hkind sourceUnit second) :
    first = second := by
  apply SourceAutHolomorphicSemiGerm.circleEquivUnitCore.symm.injective
  apply link.archimedeanTargetUnitEmbedding_injective hkind
  apply Units.ext
  let firstCircle :=
    SourceAutHolomorphicSemiGerm.circleEquivUnitCore.symm first
  let secondCircle :=
    SourceAutHolomorphicSemiGerm.circleEquivUnitCore.symm second
  calc
    (link.archimedeanTargetUnitEmbedding hkind firstCircle :
        SourceSelectedPlace.LogFieldCarrier place.1) =
        algorithm.carrierAddEquivAbove target rationalPlace place
          (link.archimedeanTargetUnitRealization hkind firstCircle) :=
      (link.archimedeanTargetUnitRealization_field hkind firstCircle).symm
    _ = algorithm.carrierAddEquivAbove target rationalPlace place
          (link.archimedeanTargetUnitRealization hkind secondCircle) :=
      congrArg (algorithm.carrierAddEquivAbove target rationalPlace place)
        (hfirst.symm.trans hsecond)
    _ = (link.archimedeanTargetUnitEmbedding hkind secondCircle :
        SourceSelectedPlace.LogFieldCarrier place.1) :=
      link.archimedeanTargetUnitRealization_field hkind secondCircle

end SourceSelectedLocalFullLogLink

/--
The Definition 1.1 full log-links on every adjacent pair in an absolute
LGP-Gaussian log-theta lattice.  These are indexed before forming tensor
packets, by the actual capsule factor and selected place.
-/
structure SourceAbsoluteLGPVerticalFullLogLinks
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
    (lattice : SourceAbsoluteLGPGaussianLogThetaLattice models)
    (algorithm : SourceMonoAnalyticLogShellAlgorithm models) where
  adjacent :
    ∀ (n m : ℤ) (label : IUTIIAbsoluteThetaLabel.{u} theta.l)
      (factor : Fin (label.tensorIndex + 1))
      (rationalPlace : SourceRationalPlace)
      (place : SourceSelectedPlaceAbove theta rationalPlace),
      SourceSelectedLocalFullLogLink algorithm
        ((lattice.siteCapsuleAtLabel n m label).object
          (lattice.sitePacketIndexEquiv n m label factor))
        ((lattice.siteCapsuleAtLabel n (m + 1) label).object
          (lattice.sitePacketIndexEquiv n (m + 1) label factor))
        rationalPlace place

namespace SourceAbsoluteLGPVerticalFullLogLinks

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
    [SourceSelectedPlaceFiberFiniteness theta]
    {lattice : SourceAbsoluteLGPGaussianLogThetaLattice models}
    {algorithm : SourceMonoAnalyticLogShellAlgorithm models}

/-- Proposition 3.5(ii)(a), derived from the selected-place full log-links. -/
noncomputable def nonarchimedeanPacketStep
    (links : SourceAbsoluteLGPVerticalFullLogLinks lattice algorithm)
    {n : ℤ}
    (family : lattice.VerticalFamilyConstruction algorithm n)
    (m : ℤ) (rationalPlace : SourceRationalPlace)
    (label : IUTIIAbsoluteThetaLabel.{u} theta.l)
    (hkind : rationalPlace.kind = .nonarchimedean) :
    SourceNonarchimedeanPacketLogLinkStep
      (lattice.siteNonarchimedeanUnitLogData algorithm n m rationalPlace
        label ((family.site m).topology rationalPlace label) hkind)
      (lattice.siteNonarchimedeanUnitLogData algorithm n (m + 1)
        rationalPlace label
        ((family.site (m + 1)).topology rationalPlace label) hkind) where
  placeEquiv := Equiv.refl _
  related factor place sourceUnit targetUnit :=
    (links.adjacent n m label factor rationalPlace place
      ).NonarchimedeanRelated hkind sourceUnit targetUnit

/-- Proposition 3.5(ii)(b), derived from the selected-place full log-links. -/
noncomputable def archimedeanPacketStep
    (links : SourceAbsoluteLGPVerticalFullLogLinks lattice algorithm)
    {n : ℤ}
    (family : lattice.VerticalFamilyConstruction algorithm n)
    (m : ℤ) (rationalPlace : SourceRationalPlace)
    (label : IUTIIAbsoluteThetaLabel.{u} theta.l)
    (hkind : rationalPlace.kind = .archimedean) :
    SourceArchimedeanPacketLogLinkStep
      (lattice.siteArchimedeanUnitData algorithm n m rationalPlace label
        ((family.site m).topology rationalPlace label)
        ((family.site m).integral rationalPlace label) hkind)
      (lattice.siteArchimedeanUnitData algorithm n (m + 1) rationalPlace
        label ((family.site (m + 1)).topology rationalPlace label)
        ((family.site (m + 1)).integral rationalPlace label) hkind) where
  placeEquiv := Equiv.refl _
  related factor place sourceUnit targetUnit :=
    (links.adjacent n m label factor rationalPlace place
      ).ArchimedeanRelated hkind sourceUnit targetUnit

/--
The complete remaining Ind3 input is now computed from Definition 1.1 full
log-links; no arbitrary packet relation is accepted at the column boundary.
-/
noncomputable def toVerticalUpperSemiData
    (links : SourceAbsoluteLGPVerticalFullLogLinks lattice algorithm)
    {n : ℤ}
    (family : lattice.VerticalFamilyConstruction algorithm n) :
    lattice.VerticalUpperSemiData family where
  nonarchLogLinkStep m rationalPlace label hkind :=
    links.nonarchimedeanPacketStep family m rationalPlace label hkind
  archLogLinkStep m rationalPlace label hkind :=
    links.archimedeanPacketStep family m rationalPlace label hkind

end SourceAbsoluteLGPVerticalFullLogLinks

end Iut
