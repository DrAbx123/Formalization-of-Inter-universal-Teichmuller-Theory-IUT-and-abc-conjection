/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceArchimedeanKummerSystem

/-!
# The `F^times-mu` prime strips of IUT II, Definition 4.9

This file packages Definition 4.9(vi)--(viii).  The finite components use the
literal model-Frobenioid reconstruction of Definition 4.9(iii)--(iv).  The
archimedean component below is universe-polymorphic and records the complete
torsion-quotient system required in Definition 4.9(v), rather than reducing it
to the universe-zero circle model.

No constructor from a theta-Hodge theater is supplied here.  Such a constructor
requires the reconstruction algorithms cited in IUT II, Corollaries 4.6 and
4.10 and remains a source theorem obligation.
-/

open CategoryTheory

namespace Iut

universe u

/-! ## Universe-polymorphic archimedean torsion quotients -/

/--
The exact compact-unit quotient system in Definition 4.9(v).

The kernel condition says that the kernel at level `N` is precisely the
`N`-torsion.  The orientation fields express that the only ambiguity in the
compatible quotient maps is the unique nonidentity automorphism of the source
compact factor.
-/
structure SourceArchimedeanTimesMuQuotientSystem
    (underlying : ArchimedeanSplitFrobenioidPresentation.{u}) where
  unitQuotient : ℕ+ -> TopologicalMonoidPresentation.{u}
  quotientMap :
    ∀ N,
      ContinuousMonoidHom
        underlying.topologicalSplitting.compactFactor
        (unitQuotient N)
  quotientMap_surjective :
    ∀ N, Function.Surjective (quotientMap N)
  unitQuotient_isUnit :
    ∀ N (value : (unitQuotient N).carrier), IsUnit value
  quotientMap_kernel :
    ∀ N value,
      quotientMap N value = 1 ↔ value ^ N.1 = 1
  transition :
    ∀ (N M : ℕ+) (_hNM : N ∣ M),
      ContinuousMonoidHom (unitQuotient N) (unitQuotient M)
  transition_quotientMap :
    ∀ (N M : ℕ+) (hNM : N ∣ M),
      (quotientMap N).comp (transition N M hNM) = quotientMap M
  transition_self :
    ∀ N,
      transition N N (dvd_refl N) =
        ContinuousMonoidHom.id (unitQuotient N)
  transition_comp :
    ∀ (N M L : ℕ+) (hNM : N ∣ M) (hML : M ∣ L),
      (transition N M hNM).comp (transition M L hML) =
        transition N L (dvd_trans hNM hML)
  orientationReversal :
    TopologicalMonoidIso
      underlying.topologicalSplitting.compactFactor
      underlying.topologicalSplitting.compactFactor
  orientationReversal_involutive :
    ∀ value,
      orientationReversal.toHom (orientationReversal.toHom value) = value
  orientationReversal_ne_identity :
    orientationReversal.toHom ≠
      ContinuousMonoidHom.id
        underlying.topologicalSplitting.compactFactor
  orientation_classification :
    ∀ automorphism :
        TopologicalMonoidIso
          underlying.topologicalSplitting.compactFactor
          underlying.topologicalSplitting.compactFactor,
      automorphism.toHom =
          ContinuousMonoidHom.id
            underlying.topologicalSplitting.compactFactor ∨
        automorphism.toHom = orientationReversal.toHom

namespace SourceArchimedeanTimesMuQuotientSystem

/-- The quotient map after the nontrivial orientation choice. -/
def reversedQuotientMap
    {underlying : ArchimedeanSplitFrobenioidPresentation.{u}}
    (quotients : SourceArchimedeanTimesMuQuotientSystem underlying)
    (N : ℕ+) :
    ContinuousMonoidHom
      underlying.topologicalSplitting.compactFactor
      (quotients.unitQuotient N) :=
  quotients.orientationReversal.toHom.comp
    (quotients.quotientMap N)

/-- Reversing orientation does not alter the exact `N`-torsion kernel. -/
theorem reversedQuotientMap_kernel
    {underlying : ArchimedeanSplitFrobenioidPresentation.{u}}
    (quotients : SourceArchimedeanTimesMuQuotientSystem underlying)
    (N : ℕ+)
    (value : underlying.topologicalSplitting.compactFactor.carrier) :
    quotients.reversedQuotientMap N value = 1 ↔ value ^ N.1 = 1 := by
  change
    quotients.quotientMap N
        (quotients.orientationReversal.toHom value) = 1 ↔
      value ^ N.1 = 1
  rw [quotients.quotientMap_kernel]
  constructor
  · intro equality
    have transported := congrArg
      quotients.orientationReversal.invHom equality
    simpa only [map_pow, map_one,
      quotients.orientationReversal.left_inv value] using transported
  · intro equality
    rw [← map_pow, equality, map_one]

/-- The reversed orientation is compatible with every quotient transition. -/
theorem transition_reversedQuotientMap
    {underlying : ArchimedeanSplitFrobenioidPresentation.{u}}
    (quotients : SourceArchimedeanTimesMuQuotientSystem underlying)
    (N M : ℕ+) (hNM : N ∣ M) :
    (quotients.reversedQuotientMap N).comp
        (quotients.transition N M hNM) =
      quotients.reversedQuotientMap M := by
  apply ContinuousMonoidHom.ext
  apply MonoidHom.ext
  intro value
  exact DFunLike.congr_fun
    (congrArg ContinuousMonoidHom.hom
      (quotients.transition_quotientMap N M hNM))
    (quotients.orientationReversal.toHom value)

/-- The transition on the compact quotient product with the fixed noncompact factor. -/
def totalTransition
    {underlying : ArchimedeanSplitFrobenioidPresentation.{u}}
    (quotients : SourceArchimedeanTimesMuQuotientSystem underlying)
    (N M : ℕ+) (hNM : N ∣ M) :
    ContinuousMonoidHom
      (TopologicalMonoidPresentation.prod
        (quotients.unitQuotient N)
        underlying.topologicalSplitting.noncompactFactor)
      (TopologicalMonoidPresentation.prod
        (quotients.unitQuotient M)
        underlying.topologicalSplitting.noncompactFactor) where
  hom :=
    { toFun := fun value =>
        (quotients.transition N M hNM value.1, value.2)
      map_one' := by
        apply Prod.ext
        · exact (quotients.transition N M hNM).hom.map_one
        · rfl
      map_mul' := by
        intro first second
        apply Prod.ext
        · exact (quotients.transition N M hNM).hom.map_mul first.1 second.1
        · rfl }
  continuous :=
    (quotients.transition N M hNM).continuous.prodMap continuous_id

end SourceArchimedeanTimesMuQuotientSystem

/-- The distinguished noncompact factor has no nonidentity units, in every universe. -/
theorem sourceTimesMuNoncompact_eq_one_of_isUnit
    (source : SplitTopologicalMonoidPresentation.{u})
    (value : source.noncompactFactor.carrier)
    (hvalue : IsUnit value) :
    value = 1 := by
  have hproduct :
      IsUnit ((1, value) :
        source.compactFactor.carrier × source.noncompactFactor.carrier) :=
    Prod.isUnit_iff.mpr ⟨isUnit_one, hvalue⟩
  have htotal :
      IsUnit (source.factorization.toHom (1, value)) :=
    hproduct.map source.factorization.toHom.hom
  obtain ⟨compact, hcompact⟩ :=
    source.every_unit_compact
      (source.factorization.toHom (1, value)) htotal
  have himage :
      source.factorization.toHom (1, value) =
        source.factorization.toHom (compact, 1) := by
    calc
      source.factorization.toHom (1, value) =
          source.compactInclusion compact := hcompact.symm
      _ = source.factorization.toHom (compact, 1) := by
        rw [source.factorization_eq]
        simp
  have hpairs : (1, value) = (compact, 1) :=
    source.factorization.left_inv.injective himage
  exact congrArg Prod.snd hpairs

/-- One reconstructed split-Frobenioid stage of the archimedean system. -/
structure SourceArchimedeanTimesMuStage
    {underlying : ArchimedeanSplitFrobenioidPresentation.{u}}
    (quotients : SourceArchimedeanTimesMuQuotientSystem underlying)
    (N : ℕ+) where
  reconstructed : ArchimedeanSplitFrobenioidPresentation.{u}
  quotientSplittingIso :
    SplitTopologicalMonoidIso
      reconstructed.topologicalSplitting
      { total :=
          TopologicalMonoidPresentation.prod
            (quotients.unitQuotient N)
            underlying.topologicalSplitting.noncompactFactor
        compactFactor := quotients.unitQuotient N
        noncompactFactor := underlying.topologicalSplitting.noncompactFactor
        compactInclusion :=
          { hom :=
              { toFun := fun value => (value, 1)
                map_one' := rfl
                map_mul' := by
                  intro first second
                  change (first * second, 1) =
                    (first * second, (1 :
                      underlying.topologicalSplitting.noncompactFactor.carrier) * 1)
                  simp }
            continuous := continuous_id.prodMk continuous_const }
        noncompactInclusion :=
          { hom :=
              { toFun := fun value => (1, value)
                map_one' := rfl
                map_mul' := by
                  intro first second
                  change (1, first * second) =
                    ((1 : (quotients.unitQuotient N).carrier) * 1,
                      first * second)
                  simp }
            continuous := continuous_const.prodMk continuous_id }
        compact_isUnit := fun value =>
          Prod.isUnit_iff.mpr
            ⟨quotients.unitQuotient_isUnit N value, isUnit_one⟩
        every_unit_compact := fun value hvalue =>
          ⟨value.1, by
            apply Prod.ext
            · rfl
            · exact (sourceTimesMuNoncompact_eq_one_of_isUnit
                underlying.topologicalSplitting value.2
                (Prod.isUnit_iff.mp hvalue).2).symm⟩
        factorization :=
          TopologicalMonoidIso.refl
            (TopologicalMonoidPresentation.prod
              (quotients.unitQuotient N)
              underlying.topologicalSplitting.noncompactFactor)
        factorization_eq := by
          intro compact noncompact
          change (compact, noncompact) =
            (compact * 1, 1 * noncompact)
          simp }
  baseEquivalence :
    CategoryTheory.Equivalence
      reconstructed.frobenioid.frobenioid.baseCategory
      underlying.frobenioid.frobenioid.baseCategory

namespace SourceArchimedeanTimesMuStage

abbrev Carrier
    {underlying : ArchimedeanSplitFrobenioidPresentation.{u}}
    {quotients : SourceArchimedeanTimesMuQuotientSystem underlying}
    {N : ℕ+} (stage : SourceArchimedeanTimesMuStage quotients N) :=
  stage.reconstructed.frobenioid.frobenioid.carrier

abbrev DivisorAt
    {underlying : ArchimedeanSplitFrobenioidPresentation.{u}}
    {quotients : SourceArchimedeanTimesMuQuotientSystem underlying}
    {N : ℕ+} (stage : SourceArchimedeanTimesMuStage quotients N)
    (X : Carrier stage) :=
  (stage.reconstructed.frobenioid.frobenioid.preFrobenioid.divisorMonoid.obj
    ((stage.reconstructed.frobenioid.frobenioid.preFrobenioid.base).obj X)).carrier

abbrev ReferenceRationalMonoid
    {underlying : ArchimedeanSplitFrobenioidPresentation.{u}}
    {quotients : SourceArchimedeanTimesMuQuotientSystem underlying}
    {N : ℕ+} (stage : SourceArchimedeanTimesMuStage quotients N) :=
  stage.reconstructed.frobenioid.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
    stage.reconstructed.referenceObject

end SourceArchimedeanTimesMuStage

/--
The complete archimedean system of Definition 4.9(v), including strict
transition laws and preservation of the Frobenioid structure.
-/
structure SourceArchimedeanTimesMuSystem
    (underlying : ArchimedeanSplitFrobenioidPresentation.{u}) where
  quotients : SourceArchimedeanTimesMuQuotientSystem underlying
  stage : ∀ N, SourceArchimedeanTimesMuStage quotients N
  carrierTransition :
    ∀ (N M : ℕ+) (_hNM : N ∣ M),
      (stage N).reconstructed.frobenioid.frobenioid.carrier ⥤
        (stage M).reconstructed.frobenioid.frobenioid.carrier
  baseTransition :
    ∀ (N M : ℕ+) (_hNM : N ∣ M),
      (stage N).reconstructed.frobenioid.frobenioid.baseCategory ⥤
        (stage M).reconstructed.frobenioid.frobenioid.baseCategory
  carrier_base_compatible :
    ∀ (N M : ℕ+) (hNM : N ∣ M),
      carrierTransition N M hNM ⋙
          (stage M).reconstructed.frobenioid.frobenioid.preFrobenioid.base =
        (stage N).reconstructed.frobenioid.frobenioid.preFrobenioid.base ⋙
          baseTransition N M hNM
  base_underlying_compatible :
    ∀ (N M : ℕ+) (hNM : N ∣ M),
      baseTransition N M hNM ⋙ (stage M).baseEquivalence.functor =
        (stage N).baseEquivalence.functor
  fsm_compatible :
    ∀ (N M : ℕ+) (hNM : N ∣ M)
      {first second :
        (stage N).reconstructed.frobenioid.frobenioid.baseCategory}
      (map : first ⟶ second),
      (stage N).reconstructed.frobenioid.frobenioid.isFSM map ->
        (stage M).reconstructed.frobenioid.frobenioid.isFSM
          ((baseTransition N M hNM).map map)
  divisorTransition :
    ∀ (N M : ℕ+) (_hNM : N ∣ M)
      (X : SourceArchimedeanTimesMuStage.Carrier (stage N)),
      SourceArchimedeanTimesMuStage.DivisorAt (stage N) X →+
        SourceArchimedeanTimesMuStage.DivisorAt (stage M)
          ((carrierTransition N M _hNM).obj X)
  divisor_compatible :
    ∀ (N M : ℕ+) (hNM : N ∣ M)
      {X Y : (stage N).reconstructed.frobenioid.frobenioid.carrier}
      (map : X ⟶ Y),
      divisorTransition N M hNM X
          ((stage N).reconstructed.frobenioid.frobenioid.preFrobenioid.divisor map) =
        (stage M).reconstructed.frobenioid.frobenioid.preFrobenioid.divisor
          ((carrierTransition N M hNM).map map)
  frobeniusDegree_compatible :
    ∀ (N M : ℕ+) (hNM : N ∣ M)
      {X Y : (stage N).reconstructed.frobenioid.frobenioid.carrier}
      (map : X ⟶ Y),
      (stage M).reconstructed.frobenioid.frobenioid.preFrobenioid.frobeniusDegree
          ((carrierTransition N M hNM).map map) =
        (stage N).reconstructed.frobenioid.frobenioid.preFrobenioid.frobeniusDegree map
  referenceIso :
    ∀ (N M : ℕ+) (hNM : N ∣ M),
      (carrierTransition N M hNM).obj
          (stage N).reconstructed.referenceObject ≅
        (stage M).reconstructed.referenceObject
  rationalTransition :
    ∀ (N M : ℕ+) (_hNM : N ∣ M),
      SourceArchimedeanTimesMuStage.ReferenceRationalMonoid (stage N) →*
        SourceArchimedeanTimesMuStage.ReferenceRationalMonoid (stage M)
  rationalTransition_hom :
    ∀ (N M : ℕ+) (hNM : N ∣ M)
      (value : SourceArchimedeanTimesMuStage.ReferenceRationalMonoid (stage N)),
      (rationalTransition N M hNM value).hom =
        (referenceIso N M hNM).inv ≫
          (carrierTransition N M hNM).map value.hom ≫
            (referenceIso N M hNM).hom
  quotient_transition_compatible :
    ∀ (N M : ℕ+) (hNM : N ∣ M)
      (value : SourceArchimedeanTimesMuStage.ReferenceRationalMonoid (stage N)),
      (stage M).quotientSplittingIso.total.toHom
          ((stage M).reconstructed.rationalTotalIso
            (rationalTransition N M hNM value)) =
        quotients.totalTransition N M hNM
          ((stage N).quotientSplittingIso.total.toHom
            ((stage N).reconstructed.rationalTotalIso value))
  carrierTransition_self :
    ∀ N,
      carrierTransition N N (dvd_refl N) =
        Functor.id ((stage N).reconstructed.frobenioid.frobenioid.carrier)
  carrierTransition_comp :
    ∀ (N M L : ℕ+) (hNM : N ∣ M) (hML : M ∣ L),
      carrierTransition N M hNM ⋙ carrierTransition M L hML =
        carrierTransition N L (dvd_trans hNM hML)
  baseTransition_self :
    ∀ N,
      baseTransition N N (dvd_refl N) =
        Functor.id ((stage N).reconstructed.frobenioid.frobenioid.baseCategory)
  baseTransition_comp :
    ∀ (N M L : ℕ+) (hNM : N ∣ M) (hML : M ∣ L),
      baseTransition N M hNM ⋙ baseTransition M L hML =
        baseTransition N L (dvd_trans hNM hML)
  rationalTransition_self :
    ∀ N,
      rationalTransition N N (dvd_refl N) =
        MonoidHom.id
          (SourceArchimedeanTimesMuStage.ReferenceRationalMonoid (stage N))
  rationalTransition_comp :
    ∀ (N M L : ℕ+) (hNM : N ∣ M) (hML : M ∣ L),
      (rationalTransition M L hML).comp
          (rationalTransition N M hNM) =
        rationalTransition N L (dvd_trans hNM hML)

namespace SourceArchimedeanTimesMuSystem

/-- The reconstructed carrier categories form the full divisibility diagram. -/
def carrierDiagram
    {underlying : ArchimedeanSplitFrobenioidPresentation.{u}}
    (system : SourceArchimedeanTimesMuSystem underlying) :
    SourceArchimedeanKummerSystem.DivisibilityIndex ⥤ Cat.{u, u} where
  obj index :=
    (system.stage index.value).reconstructed.frobenioid.frobenioid.carrier
  map {first second} arrow :=
    (system.carrierTransition first.value second.value arrow.le).toCatHom
  map_id index := by
    apply Cat.Hom.ext
    exact system.carrierTransition_self index.value
  map_comp first second := by
    apply Cat.Hom.ext
    exact (system.carrierTransition_comp _ _ _ first.le second.le).symm

/-- Restrict the complete system to any multiplicatively cofinal subset. -/
def restrictedCarrierDiagram
    {underlying : ArchimedeanSplitFrobenioidPresentation.{u}}
    (system : SourceArchimedeanTimesMuSystem underlying)
    (subset :
      SourceArchimedeanKummerSystem.MultiplicativelyCofinalSubset) :
    subset.Index ⥤ Cat.{u, u} :=
  subset.indexInclusion ⋙ system.carrierDiagram

/-- Cofinal restriction preserves and reflects the universal colimit object. -/
noncomputable def isColimitEquivRestricted
    {underlying : ArchimedeanSplitFrobenioidPresentation.{u}}
    (system : SourceArchimedeanTimesMuSystem underlying)
    (subset :
      SourceArchimedeanKummerSystem.MultiplicativelyCofinalSubset)
    (cocone : Limits.Cocone system.carrierDiagram) :
    Limits.IsColimit cocone ≃
      Limits.IsColimit (cocone.whisker subset.indexInclusion) :=
  (Functor.Final.isColimitWhiskerEquiv
    subset.indexInclusion cocone).symm

end SourceArchimedeanTimesMuSystem

/-! ## Local and global prime strips -/

/-- A selected finite place, regarded as a member of the full selected set `V`. -/
def sourceTimesMuFiniteToSelectedPlace
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    (v : SourceSelectedFinitePlace theta) :
    {place : ThetaPlace K | place ∈ theta.valuations.selectedPlaces} :=
  ⟨ThetaPlace.finite v.1,
    (theta.valuations.finite_mem_selectedPlaces_iff v.1).mpr v.2⟩

/--
The place-indexed `F^times-mu` collection of Definition 4.9(vi)--(vii).

The `finite_kind` field prevents a caller from using the good construction at
a bad place or conversely.
-/
structure SourceFTimesMuPrimeStrip
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
    (underlying : SourceFMonoAnalyticPrimeStrip models) where
  finite :
    ∀ v,
      SourceFiniteTimesMuKummerFrobenioid
        theta.l (underlying.nonarchimedean v)
  finite_kind :
    ∀ v,
      (finite v).input.kind = SourceFiniteTimesMuPlaceKind.bad ↔
        v.1 ∈ theta.valuations.bad
  archimedean :
    ∀ v,
      SourceArchimedeanTimesMuSystem (underlying.archimedean v)

namespace SourceFTimesMuPrimeStrip

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
    {underlying : SourceFMonoAnalyticPrimeStrip models}

/-- The finite `F^times` component obtained from the original `F^tilde` Frobenioid. -/
abbrev finiteUnderlyingIsometryCategory
    (_strip : SourceFTimesMuPrimeStrip underlying)
    (v : SourceSelectedFinitePlace theta) :=
  (underlying.nonarchimedean v).frobenioid.preFrobenioid.IsometryCategory

/-- The finite `F^times-mu` component obtained from the reconstructed Frobenioid. -/
abbrev finiteTimesMuIsometryCategory
    (strip : SourceFTimesMuPrimeStrip underlying)
    (v : SourceSelectedFinitePlace theta) :=
  (strip.finite v).reconstructed.frobenioid.preFrobenioid.IsometryCategory

/-- The archimedean `F^times` component of the original split Frobenioid. -/
abbrev archimedeanUnderlyingIsometryCategory
    (_strip : SourceFTimesMuPrimeStrip underlying)
    (v : SourceSelectedInfinitePlace theta) :=
  (underlying.archimedean v).frobenioid.frobenioid.preFrobenioid.IsometryCategory

/-- The archimedean `F^times-mu` component at quotient level `N`. -/
abbrev archimedeanTimesMuIsometryCategory
    (strip : SourceFTimesMuPrimeStrip underlying)
    (v : SourceSelectedInfinitePlace theta) (N : ℕ+) :=
  ((strip.archimedean v).stage N).reconstructed.frobenioid.frobenioid.preFrobenioid.IsometryCategory

/-- Transition functors preserve the literal isometry condition `divisor = 0`. -/
def archimedeanTimesMuIsometryTransition
    (strip : SourceFTimesMuPrimeStrip underlying)
    (v : SourceSelectedInfinitePlace theta)
    (N M : ℕ+) (hNM : N ∣ M) :
    strip.archimedeanTimesMuIsometryCategory v N ⥤
      strip.archimedeanTimesMuIsometryCategory v M where
  obj object :=
    ⟨((strip.archimedean v).carrierTransition N M hNM).obj object.obj⟩
  map {first second} map :=
    { hom :=
        ((strip.archimedean v).carrierTransition N M hNM).map map.hom
      property := by
        change
          (((strip.archimedean v).stage M).reconstructed.frobenioid.frobenioid.preFrobenioid.divisor
            (((strip.archimedean v).carrierTransition N M hNM).map map.hom)) = 0
        rw [← (strip.archimedean v).divisor_compatible N M hNM map.hom]
        let sourcePre :=
          ((strip.archimedean v).stage N).reconstructed.frobenioid.frobenioid.preFrobenioid
        change
          (strip.archimedean v).divisorTransition N M hNM first.obj
              (sourcePre.divisor map.hom) = 0
        rw [map.property]
        exact map_zero _ }
  map_id object := by
    apply WideSubcategory.hom_ext
    exact ((strip.archimedean v).carrierTransition N M hNM).map_id object.obj
  map_comp first second := by
    apply WideSubcategory.hom_ext
    exact ((strip.archimedean v).carrierTransition N M hNM).map_comp
      first.hom second.hom

end SourceFTimesMuPrimeStrip

/-- The literal bad selected finite places used to reconstruct the pilot. -/
def SourceFTimesMuBadPlace
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : SourceInitialThetaCore Fmod F K) :=
  {v : SourceSelectedFinitePlace theta | v.1 ∈ theta.valuations.bad}

/--
The constructive pilot-object clause of Definition 4.9(viii).

At every bad place, an actual generator of the characteristic copy of `N` is
transported to the local characteristic currency, then through `rho_v` to the
realified currency.  `reconstruct` is the global realified Frobenioid
reconstruction algorithm applied to this tuple.  Thus `pilotObject` below is
derived data, not an unrelated object field.
-/
structure SourceFTimesMuPilotReconstruction
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
    (global : SourceFGloballyRealifiedMonoAnalyticPrimeStrip models)
    (localStrip : SourceFTimesMuPrimeStrip global.monoAnalytic) where
  badGenerator :
    ∀ v : SourceFTimesMuBadPlace theta,
      (localStrip.finite v.1).input.characteristic
  badGenerator_cyclic :
    ∀ (v : SourceFTimesMuBadPlace theta)
      (value : (localStrip.finite v.1).input.characteristic),
      ∃! exponent : ℕ, value = (badGenerator v) ^ exponent
  characteristicCurrencyIso :
    ∀ v : SourceFTimesMuBadPlace theta,
      (localStrip.finite v.1).input.characteristic ≃*
        (global.characteristicLocal
          (sourceTimesMuFiniteToSelectedPlace v.1)).carrier
  reconstruct :
    (∀ v : SourceFTimesMuBadPlace theta,
      (global.realifiedLocal
        (sourceTimesMuFiniteToSelectedPlace v.1)).carrier) ->
      global.globalFrobenioid.carrier
  arithmeticDegree : global.globalFrobenioid.carrier -> ℝ
  arithmeticDegree_iso_invariant :
    ∀ {first second : global.globalFrobenioid.carrier},
      (first ≅ second) -> arithmeticDegree first = arithmeticDegree second
  pilot_negative :
    arithmeticDegree
        (reconstruct (fun v =>
          (global.rho
            (sourceTimesMuFiniteToSelectedPlace v.1)).toHom
              (characteristicCurrencyIso v (badGenerator v)))) < 0

namespace SourceFTimesMuPilotReconstruction

/-- The realified local character determined by the bad-place generators and `rho_v`. -/
def localPilotCharacter
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
    {global : SourceFGloballyRealifiedMonoAnalyticPrimeStrip models}
    {localStrip : SourceFTimesMuPrimeStrip global.monoAnalytic}
    (pilot : SourceFTimesMuPilotReconstruction global localStrip) :
    ∀ v : SourceFTimesMuBadPlace theta,
      (global.realifiedLocal
        (sourceTimesMuFiniteToSelectedPlace v.1)).carrier :=
  fun v =>
    (global.rho
      (sourceTimesMuFiniteToSelectedPlace v.1)).toHom
        (pilot.characteristicCurrencyIso v (pilot.badGenerator v))

/-- The pilot object is computed from the local character tuple. -/
def pilotObject
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
    {global : SourceFGloballyRealifiedMonoAnalyticPrimeStrip models}
    {localStrip : SourceFTimesMuPrimeStrip global.monoAnalytic}
    (pilot : SourceFTimesMuPilotReconstruction global localStrip) :
    global.globalFrobenioid.carrier :=
  pilot.reconstruct pilot.localPilotCharacter

theorem pilotObject_negative
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
    {global : SourceFGloballyRealifiedMonoAnalyticPrimeStrip models}
    {localStrip : SourceFTimesMuPrimeStrip global.monoAnalytic}
    (pilot : SourceFTimesMuPilotReconstruction global localStrip) :
    pilot.arithmeticDegree pilot.pilotObject < 0 :=
  pilot.pilot_negative

end SourceFTimesMuPilotReconstruction

/-- The globally realified `F^times-mu` prime strip of Definition 4.9(viii). -/
structure SourceFGloballyRealifiedTimesMuPrimeStrip
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
  global : SourceFGloballyRealifiedMonoAnalyticPrimeStrip models
  localStrip : SourceFTimesMuPrimeStrip global.monoAnalytic
  pilot : SourceFTimesMuPilotReconstruction global localStrip

namespace SourceFGloballyRealifiedTimesMuPrimeStrip

/-- The associated pilot is definitionally reconstructed from local generators and `rho_v`. -/
def pilotObject
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
    (strip : SourceFGloballyRealifiedTimesMuPrimeStrip models) :
    strip.global.globalFrobenioid.carrier :=
  strip.pilot.pilotObject

theorem pilotObject_negative
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
    (strip : SourceFGloballyRealifiedTimesMuPrimeStrip models) :
    strip.pilot.arithmeticDegree strip.pilotObject < 0 :=
  strip.pilot.pilotObject_negative

end SourceFGloballyRealifiedTimesMuPrimeStrip

end Iut
