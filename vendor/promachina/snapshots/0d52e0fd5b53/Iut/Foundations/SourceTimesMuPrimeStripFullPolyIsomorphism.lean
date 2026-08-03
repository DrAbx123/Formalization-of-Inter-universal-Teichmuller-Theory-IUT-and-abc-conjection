/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTimesMuPrimeStripIsomorphism

/-!
# Full poly-isomorphisms of F-times-mu prime strips

IUT I, Section 0, defines an isomorphism of categories to be an equivalence
modulo natural isomorphism and a full poly-isomorphism to be the collection of
all such isomorphisms.  IUT II, Definition 4.9(vii)--(viii), applies this
convention to isomorphisms of the complete place-indexed and globally realified
F-turnstile-times-mu collections.

This file constructs that coarsification from the structure-preserving
representatives in SourceTimesMuPrimeStripIsomorphism.  Categorical functors
are compared by natural isomorphism.  The actual group, monoid, quotient,
splitting, and local-currency maps are compared pointwise.  Compatibility
proofs and reconstruction witnesses are propositions or witnesses that certify
these principal maps, so they do not become additional morphism coordinates.
-/

open CategoryTheory

namespace Iut

universe u

/-! ## Constituent coarsifications -/

/--
Two equivalences of MLF-Galois TM pairs have the same structural map when
their three actual maps agree pointwise.
-/
structure SourceMLFGaloisTMPairEquivalence.StructurallyEqual
    {G H : TopologicalGroupCat.{u}}
    {source : SourceMLFGaloisTMPair G}
    {target : SourceMLFGaloisTMPair H}
    (first second : SourceMLFGaloisTMPairEquivalence source target) : Prop where
  group : ∀ value, first.group value = second.group value
  arithmeticMonoid :
    ∀ value, first.arithmeticMonoid value = second.arithmeticMonoid value
  unitModuloTorsion :
    ∀ value, first.unitModuloTorsion value = second.unitModuloTorsion value

namespace SourceMLFGaloisTMPairEquivalence.StructurallyEqual

variable
    {G H I J : TopologicalGroupCat.{u}}
    {source : SourceMLFGaloisTMPair G}
    {middle : SourceMLFGaloisTMPair H}
    {target : SourceMLFGaloisTMPair I}
    {final : SourceMLFGaloisTMPair J}

protected def refl
    (map : SourceMLFGaloisTMPairEquivalence source middle) :
    map.StructurallyEqual map where
  group _ := rfl
  arithmeticMonoid _ := rfl
  unitModuloTorsion _ := rfl

protected def symm
    {first second : SourceMLFGaloisTMPairEquivalence source middle}
    (relation : first.StructurallyEqual second) :
    second.StructurallyEqual first where
  group value := (relation.group value).symm
  arithmeticMonoid value := (relation.arithmeticMonoid value).symm
  unitModuloTorsion value := (relation.unitModuloTorsion value).symm

protected def trans
    {first second third : SourceMLFGaloisTMPairEquivalence source middle}
    (firstSecond : first.StructurallyEqual second)
    (secondThird : second.StructurallyEqual third) :
    first.StructurallyEqual third where
  group value :=
    (firstSecond.group value).trans (secondThird.group value)
  arithmeticMonoid value :=
    (firstSecond.arithmeticMonoid value).trans
      (secondThird.arithmeticMonoid value)
  unitModuloTorsion value :=
    (firstSecond.unitModuloTorsion value).trans
      (secondThird.unitModuloTorsion value)

/-- Composition preserves structural equality in both variables. -/
protected def comp
    {first first' : SourceMLFGaloisTMPairEquivalence source middle}
    {second second' : SourceMLFGaloisTMPairEquivalence middle target}
    (hFirst : first.StructurallyEqual first')
    (hSecond : second.StructurallyEqual second') :
    (first.trans second).StructurallyEqual (first'.trans second') where
  group value := by
    change second.group (first.group value) =
      second'.group (first'.group value)
    rw [hFirst.group, hSecond.group]
  arithmeticMonoid value := by
    change second.arithmeticMonoid (first.arithmeticMonoid value) =
      second'.arithmeticMonoid (first'.arithmeticMonoid value)
    rw [hFirst.arithmeticMonoid, hSecond.arithmeticMonoid]
  unitModuloTorsion value := by
    change second.unitModuloTorsion (first.unitModuloTorsion value) =
      second'.unitModuloTorsion (first'.unitModuloTorsion value)
    rw [hFirst.unitModuloTorsion, hSecond.unitModuloTorsion]

/-- Associativity holds after forgetting proof fields. -/
protected def assoc
    (first : SourceMLFGaloisTMPairEquivalence source middle)
    (second : SourceMLFGaloisTMPairEquivalence middle target)
    (third : SourceMLFGaloisTMPairEquivalence target final) :
    ((first.trans second).trans third).StructurallyEqual
      (first.trans (second.trans third)) where
  group _ := rfl
  arithmeticMonoid _ := rfl
  unitModuloTorsion _ := rfl

end SourceMLFGaloisTMPairEquivalence.StructurallyEqual

/-! ## Finite and archimedean system coarsifications -/

/-- The structured Section 0 relation on finite times-mu reconstructions. -/
structure SourceFiniteTimesMuKummerFrobenioidEquivalence.NaturallyIsomorphic
    {ell : PrimeGeFive}
    {sourceUnderlying targetUnderlying :
      SplitFrobenioidPresentation.{u}}
    {source :
      SourceFiniteTimesMuKummerFrobenioid ell sourceUnderlying}
    {target :
      SourceFiniteTimesMuKummerFrobenioid ell targetUnderlying}
    (first second :
      SourceFiniteTimesMuKummerFrobenioidEquivalence source target) : Prop where
  underlying :
    first.underlying.NaturallyIsomorphic second.underlying
  groupPair : first.groupPair.StructurallyEqual second.groupPair
  coverPair : first.coverPair.StructurallyEqual second.coverPair
  timesMuMonoid :
    ∀ value, first.timesMuMonoid value = second.timesMuMonoid value
  reconstructed :
    first.reconstructed.NaturallyIsomorphic second.reconstructed
  base : Nonempty (first.base.functor ≅ second.base.functor)

namespace SourceFiniteTimesMuKummerFrobenioidEquivalence.NaturallyIsomorphic

variable
    {ell : PrimeGeFive}
    {sourceUnderlying middleUnderlying targetUnderlying finalUnderlying :
      SplitFrobenioidPresentation.{u}}
    {source :
      SourceFiniteTimesMuKummerFrobenioid ell sourceUnderlying}
    {middle :
      SourceFiniteTimesMuKummerFrobenioid ell middleUnderlying}
    {target :
      SourceFiniteTimesMuKummerFrobenioid ell targetUnderlying}
    {final :
      SourceFiniteTimesMuKummerFrobenioid ell finalUnderlying}

protected def refl
    (map :
      SourceFiniteTimesMuKummerFrobenioidEquivalence source target) :
    map.NaturallyIsomorphic map where
  underlying := .refl _
  groupPair := .refl _
  coverPair := .refl _
  timesMuMonoid _ := rfl
  reconstructed := .refl _
  base := ⟨Iso.refl _⟩

protected def symm
    {first second :
      SourceFiniteTimesMuKummerFrobenioidEquivalence source target}
    (relation : first.NaturallyIsomorphic second) :
    second.NaturallyIsomorphic first where
  underlying := relation.underlying.symm
  groupPair := relation.groupPair.symm
  coverPair := relation.coverPair.symm
  timesMuMonoid value := (relation.timesMuMonoid value).symm
  reconstructed := relation.reconstructed.symm
  base := relation.base.map Iso.symm

protected def trans
    {first second third :
      SourceFiniteTimesMuKummerFrobenioidEquivalence source target}
    (firstSecond : first.NaturallyIsomorphic second)
    (secondThird : second.NaturallyIsomorphic third) :
    first.NaturallyIsomorphic third where
  underlying := firstSecond.underlying.trans secondThird.underlying
  groupPair := firstSecond.groupPair.trans secondThird.groupPair
  coverPair := firstSecond.coverPair.trans secondThird.coverPair
  timesMuMonoid value :=
    (firstSecond.timesMuMonoid value).trans
      (secondThird.timesMuMonoid value)
  reconstructed :=
    firstSecond.reconstructed.trans secondThird.reconstructed
  base := by
    rcases firstSecond.base with ⟨firstIso⟩
    rcases secondThird.base with ⟨secondIso⟩
    exact ⟨firstIso.trans secondIso⟩

/-- Composition preserves the complete finite constituent relation. -/
protected def comp
    {first first' :
      SourceFiniteTimesMuKummerFrobenioidEquivalence source middle}
    {second second' :
      SourceFiniteTimesMuKummerFrobenioidEquivalence middle target}
    (hFirst : first.NaturallyIsomorphic first')
    (hSecond : second.NaturallyIsomorphic second') :
    (first.trans second).NaturallyIsomorphic
      (first'.trans second') where
  underlying := hFirst.underlying.comp hSecond.underlying
  groupPair := hFirst.groupPair.comp hSecond.groupPair
  coverPair := hFirst.coverPair.comp hSecond.coverPair
  timesMuMonoid value := by
    change second.timesMuMonoid (first.timesMuMonoid value) =
      second'.timesMuMonoid (first'.timesMuMonoid value)
    rw [hFirst.timesMuMonoid, hSecond.timesMuMonoid]
  reconstructed := hFirst.reconstructed.comp hSecond.reconstructed
  base := by
    rcases hFirst.base with ⟨firstIso⟩
    rcases hSecond.base with ⟨secondIso⟩
    exact ⟨NatIso.hcomp firstIso secondIso⟩

/-- Associativity of finite constituent maps in the coarsification. -/
protected def assoc
    (first :
      SourceFiniteTimesMuKummerFrobenioidEquivalence source middle)
    (second :
      SourceFiniteTimesMuKummerFrobenioidEquivalence middle target)
    (third :
      SourceFiniteTimesMuKummerFrobenioidEquivalence target final) :
    ((first.trans second).trans third).NaturallyIsomorphic
      (first.trans (second.trans third)) where
  underlying := .assoc _ _ _
  groupPair := .assoc _ _ _
  coverPair := .assoc _ _ _
  timesMuMonoid _ := rfl
  reconstructed := .assoc _ _ _
  base :=
    ⟨eqToIso (Functor.assoc first.base.functor
      second.base.functor third.base.functor)⟩

end SourceFiniteTimesMuKummerFrobenioidEquivalence.NaturallyIsomorphic

/-- The structured Section 0 relation on one archimedean reconstructed stage. -/
structure SourceArchimedeanTimesMuStageEquivalence.NaturallyIsomorphic
    {sourceUnderlying targetUnderlying :
      ArchimedeanSplitFrobenioidPresentation.{u}}
    {sourceQuotients :
      SourceArchimedeanTimesMuQuotientSystem sourceUnderlying}
    {targetQuotients :
      SourceArchimedeanTimesMuQuotientSystem targetUnderlying}
    {N : ℕ+}
    {source : SourceArchimedeanTimesMuStage sourceQuotients N}
    {target : SourceArchimedeanTimesMuStage targetQuotients N}
    (first second :
      SourceArchimedeanTimesMuStageEquivalence source target) : Prop where
  reconstructed :
    first.reconstructed.NaturallyIsomorphic second.reconstructed
  base : Nonempty (first.base.functor ≅ second.base.functor)

namespace SourceArchimedeanTimesMuStageEquivalence.NaturallyIsomorphic

variable
    {sourceUnderlying middleUnderlying targetUnderlying finalUnderlying :
      ArchimedeanSplitFrobenioidPresentation.{u}}
    {sourceQuotients :
      SourceArchimedeanTimesMuQuotientSystem sourceUnderlying}
    {middleQuotients :
      SourceArchimedeanTimesMuQuotientSystem middleUnderlying}
    {targetQuotients :
      SourceArchimedeanTimesMuQuotientSystem targetUnderlying}
    {finalQuotients :
      SourceArchimedeanTimesMuQuotientSystem finalUnderlying}
    {N : ℕ+}
    {source : SourceArchimedeanTimesMuStage sourceQuotients N}
    {middle : SourceArchimedeanTimesMuStage middleQuotients N}
    {target : SourceArchimedeanTimesMuStage targetQuotients N}
    {final : SourceArchimedeanTimesMuStage finalQuotients N}

protected def refl
    (map : SourceArchimedeanTimesMuStageEquivalence source target) :
    map.NaturallyIsomorphic map where
  reconstructed := .refl _
  base := ⟨Iso.refl _⟩

protected def symm
    {first second :
      SourceArchimedeanTimesMuStageEquivalence source target}
    (relation : first.NaturallyIsomorphic second) :
    second.NaturallyIsomorphic first where
  reconstructed := relation.reconstructed.symm
  base := relation.base.map Iso.symm

protected def trans
    {first second third :
      SourceArchimedeanTimesMuStageEquivalence source target}
    (firstSecond : first.NaturallyIsomorphic second)
    (secondThird : second.NaturallyIsomorphic third) :
    first.NaturallyIsomorphic third where
  reconstructed :=
    firstSecond.reconstructed.trans secondThird.reconstructed
  base := by
    rcases firstSecond.base with ⟨firstIso⟩
    rcases secondThird.base with ⟨secondIso⟩
    exact ⟨firstIso.trans secondIso⟩

protected def comp
    {first first' :
      SourceArchimedeanTimesMuStageEquivalence source middle}
    {second second' :
      SourceArchimedeanTimesMuStageEquivalence middle target}
    (hFirst : first.NaturallyIsomorphic first')
    (hSecond : second.NaturallyIsomorphic second') :
    (first.trans second).NaturallyIsomorphic
      (first'.trans second') where
  reconstructed := hFirst.reconstructed.comp hSecond.reconstructed
  base := by
    rcases hFirst.base with ⟨firstIso⟩
    rcases hSecond.base with ⟨secondIso⟩
    exact ⟨NatIso.hcomp firstIso secondIso⟩

protected def assoc
    (first : SourceArchimedeanTimesMuStageEquivalence source middle)
    (second : SourceArchimedeanTimesMuStageEquivalence middle target)
    (third : SourceArchimedeanTimesMuStageEquivalence target final) :
    ((first.trans second).trans third).NaturallyIsomorphic
      (first.trans (second.trans third)) where
  reconstructed := .assoc _ _ _
  base :=
    ⟨eqToIso (Functor.assoc first.base.functor
      second.base.functor third.base.functor)⟩

end SourceArchimedeanTimesMuStageEquivalence.NaturallyIsomorphic

/-- The structured Section 0 relation on a complete archimedean system. -/
structure SourceArchimedeanTimesMuSystemEquivalence.NaturallyIsomorphic
    {sourceUnderlying targetUnderlying :
      ArchimedeanSplitFrobenioidPresentation.{u}}
    {source : SourceArchimedeanTimesMuSystem sourceUnderlying}
    {target : SourceArchimedeanTimesMuSystem targetUnderlying}
    (first second :
      SourceArchimedeanTimesMuSystemEquivalence source target) : Prop where
  underlying :
    first.underlying.NaturallyIsomorphic second.underlying
  unitQuotient :
    ∀ N value,
      (first.unitQuotient N).toHom value =
        (second.unitQuotient N).toHom value
  stage :
    ∀ N, (first.stage N).NaturallyIsomorphic (second.stage N)

namespace SourceArchimedeanTimesMuSystemEquivalence.NaturallyIsomorphic

variable
    {sourceUnderlying middleUnderlying targetUnderlying finalUnderlying :
      ArchimedeanSplitFrobenioidPresentation.{u}}
    {source : SourceArchimedeanTimesMuSystem sourceUnderlying}
    {middle : SourceArchimedeanTimesMuSystem middleUnderlying}
    {target : SourceArchimedeanTimesMuSystem targetUnderlying}
    {final : SourceArchimedeanTimesMuSystem finalUnderlying}

protected def refl
    (map : SourceArchimedeanTimesMuSystemEquivalence source target) :
    map.NaturallyIsomorphic map where
  underlying := .refl _
  unitQuotient _ _ := rfl
  stage _ := .refl _

protected def symm
    {first second :
      SourceArchimedeanTimesMuSystemEquivalence source target}
    (relation : first.NaturallyIsomorphic second) :
    second.NaturallyIsomorphic first where
  underlying := relation.underlying.symm
  unitQuotient N value := (relation.unitQuotient N value).symm
  stage N := (relation.stage N).symm

protected def trans
    {first second third :
      SourceArchimedeanTimesMuSystemEquivalence source target}
    (firstSecond : first.NaturallyIsomorphic second)
    (secondThird : second.NaturallyIsomorphic third) :
    first.NaturallyIsomorphic third where
  underlying :=
    firstSecond.underlying.trans secondThird.underlying
  unitQuotient N value :=
    (firstSecond.unitQuotient N value).trans
      (secondThird.unitQuotient N value)
  stage N := (firstSecond.stage N).trans (secondThird.stage N)

protected def comp
    {first first' :
      SourceArchimedeanTimesMuSystemEquivalence source middle}
    {second second' :
      SourceArchimedeanTimesMuSystemEquivalence middle target}
    (hFirst : first.NaturallyIsomorphic first')
    (hSecond : second.NaturallyIsomorphic second') :
    (first.trans second).NaturallyIsomorphic
      (first'.trans second') where
  underlying := hFirst.underlying.comp hSecond.underlying
  unitQuotient N value := by
    change
      (second.unitQuotient N).toHom
          ((first.unitQuotient N).toHom value) =
        (second'.unitQuotient N).toHom
          ((first'.unitQuotient N).toHom value)
    rw [hFirst.unitQuotient, hSecond.unitQuotient]
  stage N := (hFirst.stage N).comp (hSecond.stage N)

protected def assoc
    (first : SourceArchimedeanTimesMuSystemEquivalence source middle)
    (second : SourceArchimedeanTimesMuSystemEquivalence middle target)
    (third : SourceArchimedeanTimesMuSystemEquivalence target final) :
    ((first.trans second).trans third).NaturallyIsomorphic
      (first.trans (second.trans third)) where
  underlying := .assoc _ _ _
  unitQuotient _ _ := rfl
  stage N := .assoc (first.stage N) (second.stage N) (third.stage N)

end SourceArchimedeanTimesMuSystemEquivalence.NaturallyIsomorphic

/-- Pointwise natural isomorphism of the complete finite/infinite collection. -/
structure SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic
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
    {source : SourceFTimesMuPrimeStrip sourceUnderlying}
    {target : SourceFTimesMuPrimeStrip targetUnderlying}
    (first second : SourceFTimesMuPrimeStripEquivalence source target) :
    Prop where
  finite :
    ∀ v, (first.finite v).NaturallyIsomorphic (second.finite v)
  archimedean :
    ∀ v, (first.archimedean v).NaturallyIsomorphic (second.archimedean v)

namespace SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic

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
    {sourceUnderlying middleUnderlying targetUnderlying finalUnderlying :
      SourceFMonoAnalyticPrimeStrip models}
    {source : SourceFTimesMuPrimeStrip sourceUnderlying}
    {middle : SourceFTimesMuPrimeStrip middleUnderlying}
    {target : SourceFTimesMuPrimeStrip targetUnderlying}
    {final : SourceFTimesMuPrimeStrip finalUnderlying}

protected def refl
    (map : SourceFTimesMuPrimeStripEquivalence source target) :
    map.NaturallyIsomorphic map where
  finite _ := .refl _
  archimedean _ := .refl _

protected def symm
    {first second : SourceFTimesMuPrimeStripEquivalence source target}
    (relation : first.NaturallyIsomorphic second) :
    second.NaturallyIsomorphic first where
  finite v := (relation.finite v).symm
  archimedean v := (relation.archimedean v).symm

protected def trans
    {first second third :
      SourceFTimesMuPrimeStripEquivalence source target}
    (firstSecond : first.NaturallyIsomorphic second)
    (secondThird : second.NaturallyIsomorphic third) :
    first.NaturallyIsomorphic third where
  finite v := (firstSecond.finite v).trans (secondThird.finite v)
  archimedean v :=
    (firstSecond.archimedean v).trans (secondThird.archimedean v)

protected def comp
    {first first' : SourceFTimesMuPrimeStripEquivalence source middle}
    {second second' : SourceFTimesMuPrimeStripEquivalence middle target}
    (hFirst : first.NaturallyIsomorphic first')
    (hSecond : second.NaturallyIsomorphic second') :
    (first.trans second).NaturallyIsomorphic
      (first'.trans second') where
  finite v := (hFirst.finite v).comp (hSecond.finite v)
  archimedean v :=
    (hFirst.archimedean v).comp (hSecond.archimedean v)

protected def assoc
    (first : SourceFTimesMuPrimeStripEquivalence source middle)
    (second : SourceFTimesMuPrimeStripEquivalence middle target)
    (third : SourceFTimesMuPrimeStripEquivalence target final) :
    ((first.trans second).trans third).NaturallyIsomorphic
      (first.trans (second.trans third)) where
  finite v := .assoc (first.finite v) (second.finite v) (third.finite v)
  archimedean v :=
    .assoc (first.archimedean v) (second.archimedean v)
      (third.archimedean v)

end SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic

/-! ## Globally realified coarsification -/

/-- Natural isomorphism of the categorical maps in a global Frobenioid map. -/
structure SourceFrobenioidEquivalence.NaturallyIsomorphic
    {source target : FrobenioidPresentation.{u}}
    (first second : SourceFrobenioidEquivalence source target) : Prop where
  carrier : Nonempty (first.carrier.functor ≅ second.carrier.functor)
  base : Nonempty (first.base.functor ≅ second.base.functor)

namespace SourceFrobenioidEquivalence.NaturallyIsomorphic

variable
    {source middle target final : FrobenioidPresentation.{u}}

protected def refl
    (map : SourceFrobenioidEquivalence source target) :
    map.NaturallyIsomorphic map where
  carrier := ⟨Iso.refl _⟩
  base := ⟨Iso.refl _⟩

protected def symm
    {first second : SourceFrobenioidEquivalence source target}
    (relation : first.NaturallyIsomorphic second) :
    second.NaturallyIsomorphic first where
  carrier := relation.carrier.map Iso.symm
  base := relation.base.map Iso.symm

protected def trans
    {first second third : SourceFrobenioidEquivalence source target}
    (firstSecond : first.NaturallyIsomorphic second)
    (secondThird : second.NaturallyIsomorphic third) :
    first.NaturallyIsomorphic third where
  carrier := by
    rcases firstSecond.carrier with ⟨firstIso⟩
    rcases secondThird.carrier with ⟨secondIso⟩
    exact ⟨firstIso.trans secondIso⟩
  base := by
    rcases firstSecond.base with ⟨firstIso⟩
    rcases secondThird.base with ⟨secondIso⟩
    exact ⟨firstIso.trans secondIso⟩

protected def comp
    {first first' : SourceFrobenioidEquivalence source middle}
    {second second' : SourceFrobenioidEquivalence middle target}
    (hFirst : first.NaturallyIsomorphic first')
    (hSecond : second.NaturallyIsomorphic second') :
    (first.trans second).NaturallyIsomorphic
      (first'.trans second') where
  carrier := by
    rcases hFirst.carrier with ⟨firstIso⟩
    rcases hSecond.carrier with ⟨secondIso⟩
    exact ⟨NatIso.hcomp firstIso secondIso⟩
  base := by
    rcases hFirst.base with ⟨firstIso⟩
    rcases hSecond.base with ⟨secondIso⟩
    exact ⟨NatIso.hcomp firstIso secondIso⟩

protected def assoc
    (first : SourceFrobenioidEquivalence source middle)
    (second : SourceFrobenioidEquivalence middle target)
    (third : SourceFrobenioidEquivalence target final) :
    ((first.trans second).trans third).NaturallyIsomorphic
      (first.trans (second.trans third)) where
  carrier :=
    ⟨eqToIso (Functor.assoc first.carrier.functor
      second.carrier.functor third.carrier.functor)⟩
  base :=
    ⟨eqToIso (Functor.assoc first.base.functor
      second.base.functor third.base.functor)⟩

end SourceFrobenioidEquivalence.NaturallyIsomorphic

/--
Two globally realified representatives define the same Section 0 map when
their global and place-indexed categorical maps are naturally isomorphic and
their prime, characteristic-local, and realified-local maps agree pointwise.
-/
structure
    SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic
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
    {source target :
      SourceFGloballyRealifiedTimesMuPrimeStrip models}
    (first second :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source target) :
    Prop where
  global : first.global.NaturallyIsomorphic second.global
  prime : ∀ value, first.prime value = second.prime value
  localEquivalence :
    first.localEquivalence.NaturallyIsomorphic second.localEquivalence
  characteristicLocal :
    ∀ v value,
      (first.characteristicLocal v).toHom value =
        (second.characteristicLocal v).toHom value
  realifiedLocal :
    ∀ v value,
      (first.realifiedLocal v).toHom value =
        (second.realifiedLocal v).toHom value

namespace
    SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic

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
    {source middle target final :
      SourceFGloballyRealifiedTimesMuPrimeStrip models}

protected def refl
    (map :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source target) :
    map.NaturallyIsomorphic map where
  global := .refl _
  prime _ := rfl
  localEquivalence := .refl _
  characteristicLocal _ _ := rfl
  realifiedLocal _ _ := rfl

protected def symm
    {first second :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source target}
    (relation : first.NaturallyIsomorphic second) :
    second.NaturallyIsomorphic first where
  global := relation.global.symm
  prime value := (relation.prime value).symm
  localEquivalence := relation.localEquivalence.symm
  characteristicLocal v value :=
    (relation.characteristicLocal v value).symm
  realifiedLocal v value :=
    (relation.realifiedLocal v value).symm

protected def trans
    {first second third :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source target}
    (firstSecond : first.NaturallyIsomorphic second)
    (secondThird : second.NaturallyIsomorphic third) :
    first.NaturallyIsomorphic third where
  global := firstSecond.global.trans secondThird.global
  prime value :=
    (firstSecond.prime value).trans (secondThird.prime value)
  localEquivalence :=
    firstSecond.localEquivalence.trans secondThird.localEquivalence
  characteristicLocal v value :=
    (firstSecond.characteristicLocal v value).trans
      (secondThird.characteristicLocal v value)
  realifiedLocal v value :=
    (firstSecond.realifiedLocal v value).trans
      (secondThird.realifiedLocal v value)

/-- Composition preserves the complete globally realified relation. -/
protected def comp
    {first first' :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source middle}
    {second second' :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence middle target}
    (hFirst : first.NaturallyIsomorphic first')
    (hSecond : second.NaturallyIsomorphic second') :
    (first.trans second).NaturallyIsomorphic
      (first'.trans second') where
  global := hFirst.global.comp hSecond.global
  prime value := by
    change second.prime (first.prime value) =
      second'.prime (first'.prime value)
    rw [hFirst.prime, hSecond.prime]
  localEquivalence :=
    hFirst.localEquivalence.comp hSecond.localEquivalence
  characteristicLocal v value := by
    change
      (second.characteristicLocal v).toHom
          ((first.characteristicLocal v).toHom value) =
        (second'.characteristicLocal v).toHom
          ((first'.characteristicLocal v).toHom value)
    rw [hFirst.characteristicLocal, hSecond.characteristicLocal]
  realifiedLocal v value := by
    change
      (second.realifiedLocal v).toHom
          ((first.realifiedLocal v).toHom value) =
        (second'.realifiedLocal v).toHom
          ((first'.realifiedLocal v).toHom value)
    rw [hFirst.realifiedLocal, hSecond.realifiedLocal]

/-- Associativity of global strip isomorphisms in the coarsification. -/
protected def assoc
    (first :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source middle)
    (second :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence middle target)
    (third :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence target final) :
    ((first.trans second).trans third).NaturallyIsomorphic
      (first.trans (second.trans third)) where
  global := .assoc _ _ _
  prime _ := rfl
  localEquivalence := .assoc _ _ _
  characteristicLocal _ _ := rfl
  realifiedLocal _ _ := rfl

end
  SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic

/-! ## Unit laws for structured representatives -/

namespace SourceMLFGaloisTMPairEquivalence.StructurallyEqual

variable
    {G H : TopologicalGroupCat.{u}}
    {source : SourceMLFGaloisTMPair G}
    {target : SourceMLFGaloisTMPair H}

protected def id_comp
    (map : SourceMLFGaloisTMPairEquivalence source target) :
    ((SourceMLFGaloisTMPairEquivalence.refl source).trans map)
      |>.StructurallyEqual map where
  group _ := rfl
  arithmeticMonoid _ := rfl
  unitModuloTorsion _ := rfl

protected def comp_id
    (map : SourceMLFGaloisTMPairEquivalence source target) :
    (map.trans (SourceMLFGaloisTMPairEquivalence.refl target))
      |>.StructurallyEqual map where
  group _ := rfl
  arithmeticMonoid _ := rfl
  unitModuloTorsion _ := rfl

end SourceMLFGaloisTMPairEquivalence.StructurallyEqual

namespace SplitFrobenioidEquivalence.NaturallyIsomorphic

variable {source target : SplitFrobenioidPresentation.{u}}

protected def id_comp
    (map : SplitFrobenioidEquivalence source target) :
    ((SplitFrobenioidEquivalence.refl source).trans map)
      |>.NaturallyIsomorphic map where
  carrier :=
    ⟨eqToIso (Functor.id_comp map.carrier.functor)⟩
  splittingIndex _ := rfl

protected def comp_id
    (map : SplitFrobenioidEquivalence source target) :
    (map.trans (SplitFrobenioidEquivalence.refl target))
      |>.NaturallyIsomorphic map where
  carrier :=
    ⟨eqToIso (Functor.comp_id map.carrier.functor)⟩
  splittingIndex _ := rfl

end SplitFrobenioidEquivalence.NaturallyIsomorphic

namespace ArchimedeanSplitFrobenioidEquivalence.NaturallyIsomorphic

variable
    {source target : ArchimedeanSplitFrobenioidPresentation.{u}}

protected def id_comp
    (map : ArchimedeanSplitFrobenioidEquivalence source target) :
    ((ArchimedeanSplitFrobenioidEquivalence.refl source).trans map)
      |>.NaturallyIsomorphic map where
  frobenioid := .id_comp _
  total _ := rfl
  compactFactor _ := rfl
  noncompactFactor _ := rfl

protected def comp_id
    (map : ArchimedeanSplitFrobenioidEquivalence source target) :
    (map.trans (ArchimedeanSplitFrobenioidEquivalence.refl target))
      |>.NaturallyIsomorphic map where
  frobenioid := .comp_id _
  total _ := rfl
  compactFactor _ := rfl
  noncompactFactor _ := rfl

end ArchimedeanSplitFrobenioidEquivalence.NaturallyIsomorphic

namespace
  SourceFiniteTimesMuKummerFrobenioidEquivalence.NaturallyIsomorphic

variable
    {ell : PrimeGeFive}
    {sourceUnderlying targetUnderlying :
      SplitFrobenioidPresentation.{u}}
    {source :
      SourceFiniteTimesMuKummerFrobenioid ell sourceUnderlying}
    {target :
      SourceFiniteTimesMuKummerFrobenioid ell targetUnderlying}

protected def id_comp
    (map :
      SourceFiniteTimesMuKummerFrobenioidEquivalence source target) :
    ((SourceFiniteTimesMuKummerFrobenioidEquivalence.refl source).trans map)
      |>.NaturallyIsomorphic map where
  underlying := .id_comp _
  groupPair := .id_comp _
  coverPair := .id_comp _
  timesMuMonoid _ := rfl
  reconstructed := .id_comp _
  base := ⟨eqToIso (Functor.id_comp map.base.functor)⟩

protected def comp_id
    (map :
      SourceFiniteTimesMuKummerFrobenioidEquivalence source target) :
    (map.trans
      (SourceFiniteTimesMuKummerFrobenioidEquivalence.refl target))
      |>.NaturallyIsomorphic map where
  underlying := .comp_id _
  groupPair := .comp_id _
  coverPair := .comp_id _
  timesMuMonoid _ := rfl
  reconstructed := .comp_id _
  base := ⟨eqToIso (Functor.comp_id map.base.functor)⟩

end SourceFiniteTimesMuKummerFrobenioidEquivalence.NaturallyIsomorphic

namespace SourceArchimedeanTimesMuStageEquivalence.NaturallyIsomorphic

variable
    {sourceUnderlying targetUnderlying :
      ArchimedeanSplitFrobenioidPresentation.{u}}
    {sourceQuotients :
      SourceArchimedeanTimesMuQuotientSystem sourceUnderlying}
    {targetQuotients :
      SourceArchimedeanTimesMuQuotientSystem targetUnderlying}
    {N : ℕ+}
    {source : SourceArchimedeanTimesMuStage sourceQuotients N}
    {target : SourceArchimedeanTimesMuStage targetQuotients N}

protected def id_comp
    (map : SourceArchimedeanTimesMuStageEquivalence source target) :
    ((SourceArchimedeanTimesMuStageEquivalence.refl source).trans map)
      |>.NaturallyIsomorphic map where
  reconstructed := .id_comp _
  base := ⟨eqToIso (Functor.id_comp map.base.functor)⟩

protected def comp_id
    (map : SourceArchimedeanTimesMuStageEquivalence source target) :
    (map.trans (SourceArchimedeanTimesMuStageEquivalence.refl target))
      |>.NaturallyIsomorphic map where
  reconstructed := .comp_id _
  base := ⟨eqToIso (Functor.comp_id map.base.functor)⟩

end SourceArchimedeanTimesMuStageEquivalence.NaturallyIsomorphic

namespace SourceArchimedeanTimesMuSystemEquivalence.NaturallyIsomorphic

variable
    {sourceUnderlying targetUnderlying :
      ArchimedeanSplitFrobenioidPresentation.{u}}
    {source : SourceArchimedeanTimesMuSystem sourceUnderlying}
    {target : SourceArchimedeanTimesMuSystem targetUnderlying}

protected def id_comp
    (map : SourceArchimedeanTimesMuSystemEquivalence source target) :
    ((SourceArchimedeanTimesMuSystemEquivalence.refl source).trans map)
      |>.NaturallyIsomorphic map where
  underlying := .id_comp _
  unitQuotient _ _ := rfl
  stage N := .id_comp (map.stage N)

protected def comp_id
    (map : SourceArchimedeanTimesMuSystemEquivalence source target) :
    (map.trans (SourceArchimedeanTimesMuSystemEquivalence.refl target))
      |>.NaturallyIsomorphic map where
  underlying := .comp_id _
  unitQuotient _ _ := rfl
  stage N := .comp_id (map.stage N)

end SourceArchimedeanTimesMuSystemEquivalence.NaturallyIsomorphic

namespace SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic

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
    {sourceUnderlying targetUnderlying :
      SourceFMonoAnalyticPrimeStrip models}
    {source : SourceFTimesMuPrimeStrip sourceUnderlying}
    {target : SourceFTimesMuPrimeStrip targetUnderlying}

protected def id_comp
    (map : SourceFTimesMuPrimeStripEquivalence source target) :
    ((SourceFTimesMuPrimeStripEquivalence.refl source).trans map)
      |>.NaturallyIsomorphic map where
  finite v := .id_comp (map.finite v)
  archimedean v := .id_comp (map.archimedean v)

protected def comp_id
    (map : SourceFTimesMuPrimeStripEquivalence source target) :
    (map.trans (SourceFTimesMuPrimeStripEquivalence.refl target))
      |>.NaturallyIsomorphic map where
  finite v := .comp_id (map.finite v)
  archimedean v := .comp_id (map.archimedean v)

end SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic

namespace SourceFrobenioidEquivalence.NaturallyIsomorphic

variable {source target : FrobenioidPresentation.{u}}

protected def id_comp
    (map : SourceFrobenioidEquivalence source target) :
    ((SourceFrobenioidEquivalence.refl source).trans map)
      |>.NaturallyIsomorphic map where
  carrier := ⟨eqToIso (Functor.id_comp map.carrier.functor)⟩
  base := ⟨eqToIso (Functor.id_comp map.base.functor)⟩

protected def comp_id
    (map : SourceFrobenioidEquivalence source target) :
    (map.trans (SourceFrobenioidEquivalence.refl target))
      |>.NaturallyIsomorphic map where
  carrier := ⟨eqToIso (Functor.comp_id map.carrier.functor)⟩
  base := ⟨eqToIso (Functor.comp_id map.base.functor)⟩

end SourceFrobenioidEquivalence.NaturallyIsomorphic

namespace
  SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic

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
    {source target :
      SourceFGloballyRealifiedTimesMuPrimeStrip models}

protected def id_comp
    (map :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source target) :
    ((SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.refl source)
      |>.trans map).NaturallyIsomorphic map where
  global := .id_comp _
  prime _ := rfl
  localEquivalence := .id_comp _
  characteristicLocal _ _ := rfl
  realifiedLocal _ _ := rfl

protected def comp_id
    (map :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source target) :
    (map.trans
      (SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.refl target))
      |>.NaturallyIsomorphic map where
  global := .comp_id _
  prime _ := rfl
  localEquivalence := .comp_id _
  characteristicLocal _ _ := rfl
  realifiedLocal _ _ := rfl

end
  SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic

/-! ## Place-indexed full poly-isomorphisms -/

/-- The Section 0 setoid on place-indexed times-mu representatives. -/
def sourceFTimesMuPrimeStripEquivalenceSetoid
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
    (target : SourceFTimesMuPrimeStrip targetUnderlying) :
    Setoid (SourceFTimesMuPrimeStripEquivalence source target) where
  r := SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic
  iseqv :=
    ⟨SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.refl,
      SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.symm,
      SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.trans⟩

/-- The full poly-isomorphism of the Definition 4.9(vii) local collections. -/
abbrev SourceFTimesMuPrimeStripFullPolyIsomorphism
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
    (target : SourceFTimesMuPrimeStrip targetUnderlying) :=
  Quotient (sourceFTimesMuPrimeStripEquivalenceSetoid source target)

namespace SourceFTimesMuPrimeStripFullPolyIsomorphism

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
    {sourceUnderlying middleUnderlying targetUnderlying finalUnderlying :
      SourceFMonoAnalyticPrimeStrip models}
    {source : SourceFTimesMuPrimeStrip sourceUnderlying}
    {middle : SourceFTimesMuPrimeStrip middleUnderlying}
    {target : SourceFTimesMuPrimeStrip targetUnderlying}
    {final : SourceFTimesMuPrimeStrip finalUnderlying}

def ofEquivalence
    (map : SourceFTimesMuPrimeStripEquivalence source target) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism source target :=
  Quotient.mk _ map

noncomputable def id
    (source : SourceFTimesMuPrimeStrip sourceUnderlying) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism source source :=
  ofEquivalence (SourceFTimesMuPrimeStripEquivalence.refl source)

noncomputable def comp
    (first :
      SourceFTimesMuPrimeStripFullPolyIsomorphism source middle)
    (second :
      SourceFTimesMuPrimeStripFullPolyIsomorphism middle target) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism source target :=
  Quotient.map₂ SourceFTimesMuPrimeStripEquivalence.trans
    (by
      intro first first' hFirst second second' hSecond
      exact
        SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.comp
          hFirst hSecond)
    first second

@[simp]
theorem comp_ofEquivalence
    (first : SourceFTimesMuPrimeStripEquivalence source middle)
    (second : SourceFTimesMuPrimeStripEquivalence middle target) :
    comp (ofEquivalence first) (ofEquivalence second) =
      ofEquivalence (first.trans second) :=
  rfl

@[simp]
theorem id_comp
    (map : SourceFTimesMuPrimeStripFullPolyIsomorphism source target) :
    comp (id source) map = map := by
  refine Quotient.inductionOn map ?_
  intro representative
  apply Quotient.sound
  exact
    SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.id_comp
      representative

@[simp]
theorem comp_id
    (map : SourceFTimesMuPrimeStripFullPolyIsomorphism source target) :
    comp map (id target) = map := by
  refine Quotient.inductionOn map ?_
  intro representative
  apply Quotient.sound
  exact
    SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.comp_id
      representative

theorem comp_assoc
    (first :
      SourceFTimesMuPrimeStripFullPolyIsomorphism source middle)
    (second :
      SourceFTimesMuPrimeStripFullPolyIsomorphism middle target)
    (third :
      SourceFTimesMuPrimeStripFullPolyIsomorphism target final) :
    comp (comp first second) third =
      comp first (comp second third) := by
  refine Quotient.inductionOn₃ first second third ?_
  intro firstRepresentative secondRepresentative thirdRepresentative
  apply Quotient.sound
  exact SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.assoc
    firstRepresentative secondRepresentative thirdRepresentative

theorem representative_exists
    (map : SourceFTimesMuPrimeStripFullPolyIsomorphism source target) :
    ∃ representative : SourceFTimesMuPrimeStripEquivalence source target,
      ofEquivalence representative = map := by
  obtain ⟨representative, rfl⟩ := Quotient.exists_rep map
  exact ⟨representative, rfl⟩

theorem nonempty_iff :
    Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism source target) ↔
      Nonempty (SourceFTimesMuPrimeStripEquivalence source target) := by
  constructor
  · rintro ⟨map⟩
    obtain ⟨representative, _⟩ := representative_exists map
    exact ⟨representative⟩
  · rintro ⟨representative⟩
    exact ⟨ofEquivalence representative⟩

/-- Cancel a selected inverse pair inside a longer composite. -/
theorem comp_inverse_assoc
    {backUnderlying : SourceFMonoAnalyticPrimeStrip models}
    {back : SourceFTimesMuPrimeStrip backUnderlying}
    (forward : SourceFTimesMuPrimeStripFullPolyIsomorphism source back)
    (reverse : SourceFTimesMuPrimeStripFullPolyIsomorphism back source)
    (inverse : comp forward reverse = id source)
    (next : SourceFTimesMuPrimeStripFullPolyIsomorphism source target) :
    comp forward (comp reverse next) = next := by
  rw [← comp_assoc, inverse, id_comp]

end SourceFTimesMuPrimeStripFullPolyIsomorphism

/-! ## Globally realified full poly-isomorphisms -/

/-- The Section 0 setoid on complete globally realified representatives. -/
def sourceFGloballyRealifiedTimesMuPrimeStripEquivalenceSetoid
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
      SourceFGloballyRealifiedTimesMuPrimeStrip models) :
    Setoid
      (SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source target) where
  r :=
    SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic
  iseqv :=
    ⟨SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic.refl,
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic.symm,
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic.trans⟩

/--
The full poly-isomorphism of globally realified times-mu prime strips:
all complete structure-preserving representatives, coarsified according to
IUT I, Section 0.
-/
abbrev SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
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
      SourceFGloballyRealifiedTimesMuPrimeStrip models) :=
  Quotient
    (sourceFGloballyRealifiedTimesMuPrimeStripEquivalenceSetoid source target)

namespace SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism

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
    {source middle target final :
      SourceFGloballyRealifiedTimesMuPrimeStrip models}

/-- The class represented by one complete structure-preserving isomorphism. -/
def ofEquivalence
    (map :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source target) :
    SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism source target :=
  Quotient.mk _ map

/-- The identity member of the full poly-isomorphism. -/
noncomputable def id
    (source : SourceFGloballyRealifiedTimesMuPrimeStrip models) :
    SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism source source :=
  ofEquivalence
    (SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.refl source)

/-- Composition in the Section 0 coarsification. -/
noncomputable def comp
    (first :
      SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
        source middle)
    (second :
      SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
        middle target) :
    SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
      source target :=
  Quotient.map₂
    SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.trans
    (by
      intro first first' hFirst second second' hSecond
      exact
        SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic.comp
          hFirst hSecond)
    first second

@[simp]
theorem comp_ofEquivalence
    (first :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source middle)
    (second :
      SourceFGloballyRealifiedTimesMuPrimeStripEquivalence middle target) :
    comp (ofEquivalence first) (ofEquivalence second) =
      ofEquivalence (first.trans second) :=
  rfl

@[simp]
theorem id_comp
    (map :
      SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
        source target) :
    comp (id source) map = map := by
  refine Quotient.inductionOn map ?_
  intro representative
  apply Quotient.sound
  exact
    SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic.id_comp
      representative

@[simp]
theorem comp_id
    (map :
      SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
        source target) :
    comp map (id target) = map := by
  refine Quotient.inductionOn map ?_
  intro representative
  apply Quotient.sound
  exact
    SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic.comp_id
      representative

theorem comp_assoc
    (first :
      SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
        source middle)
    (second :
      SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
        middle target)
    (third :
      SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
        target final) :
    comp (comp first second) third =
      comp first (comp second third) := by
  refine Quotient.inductionOn₃ first second third ?_
  intro firstRepresentative secondRepresentative thirdRepresentative
  apply Quotient.sound
  exact
    SourceFGloballyRealifiedTimesMuPrimeStripEquivalence.NaturallyIsomorphic.assoc
      firstRepresentative secondRepresentative thirdRepresentative

/-- Every coarsified member has a complete structure-preserving representative. -/
theorem representative_exists
    (map :
      SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
        source target) :
    ∃ representative :
        SourceFGloballyRealifiedTimesMuPrimeStripEquivalence source target,
      ofEquivalence representative = map := by
  obtain ⟨representative, rfl⟩ := Quotient.exists_rep map
  exact ⟨representative, rfl⟩

/-- The full poly-isomorphism is nonempty exactly when a representative exists. -/
theorem nonempty_iff :
    Nonempty
        (SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
          source target) ↔
      Nonempty
        (SourceFGloballyRealifiedTimesMuPrimeStripEquivalence
          source target) := by
  constructor
  · rintro ⟨map⟩
    obtain ⟨representative, _⟩ := representative_exists map
    exact ⟨representative⟩
  · rintro ⟨representative⟩
    exact ⟨ofEquivalence representative⟩

/-- Cancel a selected inverse pair inside a longer composite. -/
theorem comp_inverse_assoc
    (forward :
      SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
        source middle)
    (back :
      SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
        middle source)
    (inverse : comp forward back = id source)
    (next :
      SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism
        source target) :
    comp forward (comp back next) = next := by
  rw [← comp_assoc, inverse, id_comp]

end SourceFGloballyRealifiedTimesMuPrimeStripFullPolyIsomorphism

end Iut
