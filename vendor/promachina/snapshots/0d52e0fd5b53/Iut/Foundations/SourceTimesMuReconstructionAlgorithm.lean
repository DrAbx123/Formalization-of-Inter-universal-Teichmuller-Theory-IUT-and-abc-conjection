/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTimesMuPrimeStripFullPolyIsomorphism

/-!
# The functorial times-mu reconstruction algorithm

This file formalizes the functorial algorithm cited in IUT II,
Definition 4.9(vi) and Corollary 4.10(iii)--(iv).  Its objects are assembled
place by place from the exact finite and archimedean reconstruction outputs.
Its maps are assembled componentwise from the corresponding
structure-preserving equivalences.  Coherence is stated in the Section 0
coarsification, so the algorithm induces an honest map on full
poly-isomorphisms.

The records below are still a source boundary: they do not prove the finite
model-Frobenioid reconstruction theorem or construct the archimedean
torsion-quotient system.  They do prevent those obligations from being
replaced by an unrelated prime-strip output or an unstructured map.
-/

namespace Iut

universe u

/-! ## Structure-preserving maps of mono-analytic prime strips -/

/-- A componentwise structure-preserving equivalence of mono-analytic `F`-prime-strips. -/
structure SourceFMonoAnalyticPrimeStripEquivalence
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
    (source target : SourceFMonoAnalyticPrimeStrip models) where
  finite :
    ∀ v, SplitFrobenioidEquivalence
      (source.nonarchimedean v) (target.nonarchimedean v)
  archimedean :
    ∀ v, ArchimedeanSplitFrobenioidEquivalence
      (source.archimedean v) (target.archimedean v)

namespace SourceFMonoAnalyticPrimeStripEquivalence

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
    {source middle target final : SourceFMonoAnalyticPrimeStrip models}

/-- The common Examples 3.2--3.4 mono-analytic model prime strip. -/
def model
    (models : IUTIThetaHodgeTheaterModels theta) :
    SourceFMonoAnalyticPrimeStrip models where
  nonarchimedean v := (models.nonarchimedean v).fTildeSplit
  nonarchimedeanEquivalence v :=
    SplitFrobenioidEquivalence.refl
      (models.nonarchimedean v).fTildeSplit
  nonarchimedeanEquivalenceFromModel v :=
    SplitFrobenioidEquivalence.refl
      (models.nonarchimedean v).fTildeSplit
  nonarchimedeanToFrom v :=
    SplitFrobenioidEquivalence.NaturallyIsomorphic.id_comp
      (SplitFrobenioidEquivalence.refl
        (models.nonarchimedean v).fTildeSplit)
  nonarchimedeanFromTo v :=
    SplitFrobenioidEquivalence.NaturallyIsomorphic.id_comp
      (SplitFrobenioidEquivalence.refl
        (models.nonarchimedean v).fTildeSplit)
  archimedean v := (models.archimedean v).fTildeMonoAnalytic
  archimedeanEquivalence v :=
    ArchimedeanSplitFrobenioidEquivalence.refl
      (models.archimedean v).fTildeMonoAnalytic
  archimedeanEquivalenceFromModel v :=
    ArchimedeanSplitFrobenioidEquivalence.refl
      (models.archimedean v).fTildeMonoAnalytic
  archimedeanToFrom v :=
    ArchimedeanSplitFrobenioidEquivalence.NaturallyIsomorphic.id_comp
      (ArchimedeanSplitFrobenioidEquivalence.refl
        (models.archimedean v).fTildeMonoAnalytic)
  archimedeanFromTo v :=
    ArchimedeanSplitFrobenioidEquivalence.NaturallyIsomorphic.id_comp
      (ArchimedeanSplitFrobenioidEquivalence.refl
        (models.archimedean v).fTildeMonoAnalytic)

/-- Identity mono-analytic prime-strip equivalence. -/
def refl (source : SourceFMonoAnalyticPrimeStrip models) :
    SourceFMonoAnalyticPrimeStripEquivalence source source where
  finite v := SplitFrobenioidEquivalence.refl (source.nonarchimedean v)
  archimedean v :=
    ArchimedeanSplitFrobenioidEquivalence.refl (source.archimedean v)

/-- The fixed comparison from a mono-analytic strip to the common model. -/
def toModel (source : SourceFMonoAnalyticPrimeStrip models) :
    SourceFMonoAnalyticPrimeStripEquivalence source
      (model models) where
  finite v := source.nonarchimedeanEquivalence v
  archimedean v := source.archimedeanEquivalence v

/-- The fixed inverse comparison from the common model to a strip. -/
def fromModel (target : SourceFMonoAnalyticPrimeStrip models) :
    SourceFMonoAnalyticPrimeStripEquivalence
      (model models) target where
  finite v := target.nonarchimedeanEquivalenceFromModel v
  archimedean v := target.archimedeanEquivalenceFromModel v

/-- Composition of mono-analytic prime-strip equivalences. -/
def trans
    (first : SourceFMonoAnalyticPrimeStripEquivalence source middle)
    (second : SourceFMonoAnalyticPrimeStripEquivalence middle target) :
    SourceFMonoAnalyticPrimeStripEquivalence source target where
  finite v := (first.finite v).trans (second.finite v)
  archimedean v := (first.archimedean v).trans (second.archimedean v)

/--
The canonical member of the full mono-analytic theta link, obtained by
transporting both exact theater strips through their common source model.
-/
def canonical
    (source target : SourceFMonoAnalyticPrimeStrip models) :
    SourceFMonoAnalyticPrimeStripEquivalence source target :=
  (toModel source).trans (fromModel target)

/--
Natural isomorphism of mono-analytic prime-strip equivalences.  Only the
categorical equivalence coordinates are coarsified; the other structural maps
remain pointwise coordinates of the component relations.
-/
structure NaturallyIsomorphic
    (first second : SourceFMonoAnalyticPrimeStripEquivalence source target) :
    Prop where
  finite :
    ∀ v, SplitFrobenioidEquivalence.NaturallyIsomorphic
      (first.finite v) (second.finite v)
  archimedean :
    ∀ v, ArchimedeanSplitFrobenioidEquivalence.NaturallyIsomorphic
      (first.archimedean v) (second.archimedean v)

namespace NaturallyIsomorphic

/-- Reflexivity of structured natural isomorphism. -/
protected theorem refl
    (map : SourceFMonoAnalyticPrimeStripEquivalence source target) :
    map.NaturallyIsomorphic map where
  finite v :=
    SplitFrobenioidEquivalence.NaturallyIsomorphic.refl (map.finite v)
  archimedean v :=
    ArchimedeanSplitFrobenioidEquivalence.NaturallyIsomorphic.refl
      (map.archimedean v)

/-- Symmetry of structured natural isomorphism. -/
protected theorem symm
    {first second : SourceFMonoAnalyticPrimeStripEquivalence source target}
    (relation : first.NaturallyIsomorphic second) :
    second.NaturallyIsomorphic first where
  finite v := (relation.finite v).symm
  archimedean v := (relation.archimedean v).symm

/-- Transitivity of structured natural isomorphism. -/
protected theorem trans
    {first second third : SourceFMonoAnalyticPrimeStripEquivalence source target}
    (firstSecond : first.NaturallyIsomorphic second)
    (secondThird : second.NaturallyIsomorphic third) :
    first.NaturallyIsomorphic third where
  finite v := (firstSecond.finite v).trans (secondThird.finite v)
  archimedean v :=
    (firstSecond.archimedean v).trans (secondThird.archimedean v)

/-- Structured natural isomorphisms are preserved by composition. -/
theorem comp
    {first first' : SourceFMonoAnalyticPrimeStripEquivalence source middle}
    {second second' : SourceFMonoAnalyticPrimeStripEquivalence middle target}
    (hFirst : first.NaturallyIsomorphic first')
    (hSecond : second.NaturallyIsomorphic second') :
    (first.trans second).NaturallyIsomorphic (first'.trans second') where
  finite v :=
    SplitFrobenioidEquivalence.NaturallyIsomorphic.comp
      (hFirst.finite v) (hSecond.finite v)
  archimedean v :=
    ArchimedeanSplitFrobenioidEquivalence.NaturallyIsomorphic.comp
      (hFirst.archimedean v) (hSecond.archimedean v)

/-- Left identity is naturally isomorphic to the original map. -/
theorem id_comp
    (map : SourceFMonoAnalyticPrimeStripEquivalence source target) :
    ((refl source).trans map).NaturallyIsomorphic map where
  finite v :=
    SplitFrobenioidEquivalence.NaturallyIsomorphic.id_comp (map.finite v)
  archimedean v :=
    ArchimedeanSplitFrobenioidEquivalence.NaturallyIsomorphic.id_comp
      (map.archimedean v)

/-- Right identity is naturally isomorphic to the original map. -/
theorem comp_id
    (map : SourceFMonoAnalyticPrimeStripEquivalence source target) :
    (map.trans (refl target)).NaturallyIsomorphic map where
  finite v :=
    SplitFrobenioidEquivalence.NaturallyIsomorphic.comp_id (map.finite v)
  archimedean v :=
    ArchimedeanSplitFrobenioidEquivalence.NaturallyIsomorphic.comp_id
      (map.archimedean v)

/-- Associativity holds up to structured natural isomorphism. -/
theorem assoc
    (first : SourceFMonoAnalyticPrimeStripEquivalence source middle)
    (second : SourceFMonoAnalyticPrimeStripEquivalence middle target)
    (third : SourceFMonoAnalyticPrimeStripEquivalence target final) :
    ((first.trans second).trans third).NaturallyIsomorphic
      (first.trans (second.trans third)) where
  finite v :=
    SplitFrobenioidEquivalence.NaturallyIsomorphic.assoc
      (first.finite v) (second.finite v) (third.finite v)
  archimedean v :=
    ArchimedeanSplitFrobenioidEquivalence.NaturallyIsomorphic.assoc
      (first.archimedean v) (second.archimedean v) (third.archimedean v)

end NaturallyIsomorphic

end SourceFMonoAnalyticPrimeStripEquivalence

/-! ## Section 0 coarsification of mono-analytic prime strips -/

/-- The Section 0 setoid on complete mono-analytic equivalence representatives. -/
def sourceFMonoAnalyticPrimeStripEquivalenceSetoid
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
    (source target : SourceFMonoAnalyticPrimeStrip models) :
    Setoid (SourceFMonoAnalyticPrimeStripEquivalence source target) where
  r := SourceFMonoAnalyticPrimeStripEquivalence.NaturallyIsomorphic
  iseqv :=
    ⟨SourceFMonoAnalyticPrimeStripEquivalence.NaturallyIsomorphic.refl,
      SourceFMonoAnalyticPrimeStripEquivalence.NaturallyIsomorphic.symm,
      SourceFMonoAnalyticPrimeStripEquivalence.NaturallyIsomorphic.trans⟩

/-- The full poly-isomorphism of mono-analytic prime strips. -/
abbrev SourceFMonoAnalyticPrimeStripFullPolyIsomorphism
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
    (source target : SourceFMonoAnalyticPrimeStrip models) :=
  Quotient (sourceFMonoAnalyticPrimeStripEquivalenceSetoid source target)

namespace SourceFMonoAnalyticPrimeStripFullPolyIsomorphism

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
    {source middle target final : SourceFMonoAnalyticPrimeStrip models}

/-- Coarsify one complete representative. -/
def ofEquivalence
    (map : SourceFMonoAnalyticPrimeStripEquivalence source target) :
    SourceFMonoAnalyticPrimeStripFullPolyIsomorphism source target :=
  Quotient.mk _ map

/-- Identity full poly-isomorphism. -/
def id (source : SourceFMonoAnalyticPrimeStrip models) :
    SourceFMonoAnalyticPrimeStripFullPolyIsomorphism source source :=
  ofEquivalence (SourceFMonoAnalyticPrimeStripEquivalence.refl source)

/-- The canonical member of the full theta-link poly-isomorphism. -/
def canonical
    (source target : SourceFMonoAnalyticPrimeStrip models) :
    SourceFMonoAnalyticPrimeStripFullPolyIsomorphism source target :=
  ofEquivalence
    (SourceFMonoAnalyticPrimeStripEquivalence.canonical source target)

/-- Composition of full poly-isomorphisms. -/
def comp
    (first : SourceFMonoAnalyticPrimeStripFullPolyIsomorphism source middle)
    (second : SourceFMonoAnalyticPrimeStripFullPolyIsomorphism middle target) :
    SourceFMonoAnalyticPrimeStripFullPolyIsomorphism source target :=
  Quotient.map₂ SourceFMonoAnalyticPrimeStripEquivalence.trans
    (by
      intro first first' hFirst second second' hSecond
      exact
        SourceFMonoAnalyticPrimeStripEquivalence.NaturallyIsomorphic.comp
          hFirst hSecond)
    first second

@[simp]
theorem id_comp
    (map : SourceFMonoAnalyticPrimeStripFullPolyIsomorphism source target) :
    comp (id source) map = map := by
  refine Quotient.inductionOn map ?_
  intro representative
  apply Quotient.sound
  exact
    SourceFMonoAnalyticPrimeStripEquivalence.NaturallyIsomorphic.id_comp
      representative

@[simp]
theorem comp_id
    (map : SourceFMonoAnalyticPrimeStripFullPolyIsomorphism source target) :
    comp map (id target) = map := by
  refine Quotient.inductionOn map ?_
  intro representative
  apply Quotient.sound
  exact
    SourceFMonoAnalyticPrimeStripEquivalence.NaturallyIsomorphic.comp_id
      representative

theorem comp_assoc
    (first : SourceFMonoAnalyticPrimeStripFullPolyIsomorphism source middle)
    (second : SourceFMonoAnalyticPrimeStripFullPolyIsomorphism middle target)
    (third : SourceFMonoAnalyticPrimeStripFullPolyIsomorphism target final) :
    comp (comp first second) third = comp first (comp second third) := by
  refine Quotient.inductionOn₃ first second third ?_
  intro firstRepresentative secondRepresentative thirdRepresentative
  apply Quotient.sound
  exact
    SourceFMonoAnalyticPrimeStripEquivalence.NaturallyIsomorphic.assoc
      firstRepresentative secondRepresentative thirdRepresentative

/-- A strip-to-model comparison followed by its fixed inverse is identity. -/
theorem toModel_fromModel
    (source : SourceFMonoAnalyticPrimeStrip models) :
    comp
        (ofEquivalence
          (SourceFMonoAnalyticPrimeStripEquivalence.toModel source))
        (ofEquivalence
          (SourceFMonoAnalyticPrimeStripEquivalence.fromModel source)) =
      id source := by
  apply Quotient.sound
  exact
    { finite := source.nonarchimedeanToFrom
      archimedean := source.archimedeanToFrom }

/-- A model-to-strip comparison followed by its fixed inverse is identity. -/
theorem fromModel_toModel
    (source : SourceFMonoAnalyticPrimeStrip models) :
    comp
        (ofEquivalence
          (SourceFMonoAnalyticPrimeStripEquivalence.fromModel source))
        (ofEquivalence
          (SourceFMonoAnalyticPrimeStripEquivalence.toModel source)) =
      id (SourceFMonoAnalyticPrimeStripEquivalence.model models) := by
  apply Quotient.sound
  exact
    { finite := source.nonarchimedeanFromTo
      archimedean := source.archimedeanFromTo }

/-- Canonical comparisons through the common model are selected inverses. -/
theorem canonical_inverse
    (source target : SourceFMonoAnalyticPrimeStrip models) :
    comp (canonical source target) (canonical target source) =
      id source := by
  change
    comp
        (comp
          (ofEquivalence
            (SourceFMonoAnalyticPrimeStripEquivalence.toModel source))
          (ofEquivalence
            (SourceFMonoAnalyticPrimeStripEquivalence.fromModel target)))
        (comp
          (ofEquivalence
            (SourceFMonoAnalyticPrimeStripEquivalence.toModel target))
          (ofEquivalence
            (SourceFMonoAnalyticPrimeStripEquivalence.fromModel source))) =
      id source
  simp only [comp_assoc]
  rw [← comp_assoc
    (ofEquivalence
      (SourceFMonoAnalyticPrimeStripEquivalence.fromModel target))
    (ofEquivalence
      (SourceFMonoAnalyticPrimeStripEquivalence.toModel target))
    (ofEquivalence
      (SourceFMonoAnalyticPrimeStripEquivalence.fromModel source))]
  rw [fromModel_toModel target]
  rw [id_comp]
  exact toModel_fromModel source

end SourceFMonoAnalyticPrimeStripFullPolyIsomorphism

/-! ## Object reconstruction and functorial transport -/

/--
The object part of Definition 4.9(vi), assembled from exact component
reconstructions at every selected place.
-/
structure SourceFTimesMuReconstructionObjects
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    (models : IUTIThetaHodgeTheaterModels theta) where
  finite :
    ∀ (underlying : SourceFMonoAnalyticPrimeStrip models) v,
      SourceFiniteTimesMuKummerFrobenioid
        theta.l (underlying.nonarchimedean v)
  finite_kind :
    ∀ (underlying : SourceFMonoAnalyticPrimeStrip models) v,
      (finite underlying v).input.kind = SourceFiniteTimesMuPlaceKind.bad ↔
        v.1 ∈ theta.valuations.bad
  archimedean :
    ∀ (underlying : SourceFMonoAnalyticPrimeStrip models) v,
      SourceArchimedeanTimesMuSystem (underlying.archimedean v)

namespace SourceFTimesMuReconstructionObjects

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

/-- The place-indexed times-mu strip computed by the object algorithm. -/
def obj
    (objects : SourceFTimesMuReconstructionObjects models)
    (underlying : SourceFMonoAnalyticPrimeStrip models) :
    SourceFTimesMuPrimeStrip underlying where
  finite := objects.finite underlying
  finite_kind := objects.finite_kind underlying
  archimedean := objects.archimedean underlying

end SourceFTimesMuReconstructionObjects

/--
The componentwise map part of the reconstruction algorithm.  The output map
is derived below; it is not an independent whole-strip field.
-/
structure SourceFTimesMuReconstructionTransport
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
    (objects : SourceFTimesMuReconstructionObjects models) where
  finite :
    ∀ {source target : SourceFMonoAnalyticPrimeStrip models}
      (map : SourceFMonoAnalyticPrimeStripEquivalence source target) v,
      {lift : SourceFiniteTimesMuKummerFrobenioidEquivalence
          (objects.finite source v) (objects.finite target v) //
        lift.underlying = map.finite v}
  archimedean :
    ∀ {source target : SourceFMonoAnalyticPrimeStrip models}
      (map : SourceFMonoAnalyticPrimeStripEquivalence source target) v,
      {lift : SourceArchimedeanTimesMuSystemEquivalence
          (objects.archimedean source v) (objects.archimedean target v) //
        lift.underlying = map.archimedean v}

namespace SourceFTimesMuReconstructionTransport

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
    {objects : SourceFTimesMuReconstructionObjects models}

/-- Assemble the component transports into a complete times-mu equivalence. -/
def map
    (transport : SourceFTimesMuReconstructionTransport objects)
    {source target : SourceFMonoAnalyticPrimeStrip models}
    (sourceMap : SourceFMonoAnalyticPrimeStripEquivalence source target) :
    SourceFTimesMuPrimeStripEquivalence
      (objects.obj source) (objects.obj target) where
  finite v := (transport.finite sourceMap v).1
  archimedean v := (transport.archimedean sourceMap v).1

end SourceFTimesMuReconstructionTransport

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
    {source target : SourceFMonoAnalyticPrimeStrip models}
    {sourceTimesMu : SourceFTimesMuPrimeStrip source}
    {targetTimesMu : SourceFTimesMuPrimeStrip target}

/--
Forget the reconstructed Kummer, quotient, and Frobenioid coordinates of a
times-mu equivalence.  The remaining finite and archimedean maps form the
underlying mono-analytic prime-strip equivalence.
-/
def underlying
    (map : SourceFTimesMuPrimeStripEquivalence
      sourceTimesMu targetTimesMu) :
    SourceFMonoAnalyticPrimeStripEquivalence source target where
  finite v := (map.finite v).underlying
  archimedean v := (map.archimedean v).underlying

end SourceFTimesMuPrimeStripEquivalence

/--
Functorial coherence for the componentwise reconstruction transport.
The congruence field is what makes the map descend to Section 0 classes.
-/
structure SourceFTimesMuReconstructionFunctoriality
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
    (objects : SourceFTimesMuReconstructionObjects models)
    (transport : SourceFTimesMuReconstructionTransport objects) where
  congruent :
    ∀ {source target : SourceFMonoAnalyticPrimeStrip models}
      {first second : SourceFMonoAnalyticPrimeStripEquivalence source target},
      first.NaturallyIsomorphic second →
        (transport.map first).NaturallyIsomorphic (transport.map second)
  map_refl :
    ∀ source : SourceFMonoAnalyticPrimeStrip models,
      (transport.map (SourceFMonoAnalyticPrimeStripEquivalence.refl source)
        ).NaturallyIsomorphic
          (SourceFTimesMuPrimeStripEquivalence.refl (objects.obj source))
  map_trans :
    ∀ {source middle target : SourceFMonoAnalyticPrimeStrip models}
      (first : SourceFMonoAnalyticPrimeStripEquivalence source middle)
      (second : SourceFMonoAnalyticPrimeStripEquivalence middle target),
      (transport.map (first.trans second)).NaturallyIsomorphic
        ((transport.map first).trans (transport.map second))

/--
The Corollary 4.10(iv) fullness property of unit-portion reconstruction.

For every complete equivalence of two reconstructed times-mu objects, lifting
its underlying mono-analytic equivalence recovers the original map up to the
Section 0 structured natural-isomorphism relation.  This representative-level
statement is strictly stronger than functoriality and implies that the induced
map on full poly-isomorphism classes is surjective.
-/
structure SourceFTimesMuReconstructionFullness
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
    (objects : SourceFTimesMuReconstructionObjects models)
    (transport : SourceFTimesMuReconstructionTransport objects)
    (source target : SourceFMonoAnalyticPrimeStrip models) where
  map_underlying :
    ∀ output : SourceFTimesMuPrimeStripEquivalence
        (objects.obj source) (objects.obj target),
      (transport.map output.underlying).NaturallyIsomorphic output

/-- The complete functorial algorithm of Definition 4.9(vi). -/
structure SourceFTimesMuReconstructionAlgorithm
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    (models : IUTIThetaHodgeTheaterModels theta) where
  objects : SourceFTimesMuReconstructionObjects models
  transport : SourceFTimesMuReconstructionTransport objects
  functoriality :
    SourceFTimesMuReconstructionFunctoriality objects transport

namespace SourceFTimesMuReconstructionAlgorithm

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
    (algorithm : SourceFTimesMuReconstructionAlgorithm models)

/-- The reconstructed times-mu object. -/
def obj (underlying : SourceFMonoAnalyticPrimeStrip models) :
    SourceFTimesMuPrimeStrip underlying :=
  algorithm.objects.obj underlying

/-- The reconstructed structure-preserving equivalence. -/
def map
    {source target : SourceFMonoAnalyticPrimeStrip models}
    (sourceMap : SourceFMonoAnalyticPrimeStripEquivalence source target) :
    SourceFTimesMuPrimeStripEquivalence
      (algorithm.obj source) (algorithm.obj target) :=
  algorithm.transport.map sourceMap

/-- The algorithm descends to full poly-isomorphism classes. -/
def mapFullPolyIsomorphism
    {source target : SourceFMonoAnalyticPrimeStrip models}
    (sourceMap :
      SourceFMonoAnalyticPrimeStripFullPolyIsomorphism source target) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism
      (algorithm.obj source) (algorithm.obj target) :=
  Quotient.map algorithm.map
    (by
      intro first second relation
      exact algorithm.functoriality.congruent relation)
    sourceMap

/-- The induced map preserves the identity class. -/
@[simp]
theorem mapFullPolyIsomorphism_id
    (source : SourceFMonoAnalyticPrimeStrip models) :
    algorithm.mapFullPolyIsomorphism
        (SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.id source) =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.id
        (algorithm.obj source) := by
  apply Quotient.sound
  exact algorithm.functoriality.map_refl source

/-- The induced map preserves composition of full poly-isomorphisms. -/
theorem mapFullPolyIsomorphism_comp
    {source middle target : SourceFMonoAnalyticPrimeStrip models}
    (first : SourceFMonoAnalyticPrimeStripFullPolyIsomorphism source middle)
    (second : SourceFMonoAnalyticPrimeStripFullPolyIsomorphism middle target) :
    algorithm.mapFullPolyIsomorphism
        (SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.comp first second) =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
        (algorithm.mapFullPolyIsomorphism first)
        (algorithm.mapFullPolyIsomorphism second) := by
  refine Quotient.inductionOn₂ first second ?_
  intro firstRepresentative secondRepresentative
  apply Quotient.sound
  exact algorithm.functoriality.map_trans
    firstRepresentative secondRepresentative

/--
Corollary 4.10(iv): the map induced by unit-portion reconstruction has the
entire output full poly-isomorphism as its image.
-/
theorem mapFullPolyIsomorphism_surjective
    {source target : SourceFMonoAnalyticPrimeStrip models}
    (fullness : SourceFTimesMuReconstructionFullness
      algorithm.objects algorithm.transport source target) :
    Function.Surjective
      (fun sourceMap :
          SourceFMonoAnalyticPrimeStripFullPolyIsomorphism source target =>
        algorithm.mapFullPolyIsomorphism sourceMap) := by
  intro output
  refine Quotient.inductionOn output ?_
  intro representative
  refine ⟨SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.ofEquivalence
      representative.underlying, ?_⟩
  apply Quotient.sound
  exact fullness.map_underlying representative

/-- A selected inverse pair remains an inverse pair after reconstruction. -/
theorem mapFullPolyIsomorphism_inverse
    {source target : SourceFMonoAnalyticPrimeStrip models}
    (forward : SourceFMonoAnalyticPrimeStripFullPolyIsomorphism source target)
    (reverse : SourceFMonoAnalyticPrimeStripFullPolyIsomorphism target source)
    (inverse :
      SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.comp forward reverse =
        SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.id source) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
        (algorithm.mapFullPolyIsomorphism forward)
        (algorithm.mapFullPolyIsomorphism reverse) =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.id
        (algorithm.obj source) := by
  rw [← algorithm.mapFullPolyIsomorphism_comp, inverse]
  exact algorithm.mapFullPolyIsomorphism_id source

end SourceFTimesMuReconstructionAlgorithm

end Iut
