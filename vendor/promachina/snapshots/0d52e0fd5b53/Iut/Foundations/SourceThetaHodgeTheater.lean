/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.Frobenioid
import Iut.Foundations.Procession
import Iut.Foundations.SourceInitialThetaDefinition
import Mathlib.Topology.Algebra.Monoid.Defs

/-!
# Source boundary for IUT I theta-Hodge theaters

This module translates the data clauses of IUT I, Definition 3.6 into Lean.
It is intentionally an obligation interface: there is no constructor from
`SourceInitialThetaCore` until the local and global Frobenioid models cited in
Examples 3.2-3.5 have actually been constructed.

The older degree-preorder experiment lives in `ThetaHodgeTheater.lean` under
names prefixed by `Toy`; it is not imported here.
-/

open CategoryTheory

namespace Iut

universe u

/-- A topological monoid packaged without forgetting its topology. -/
structure TopologicalMonoidPresentation where
  carrier : Type u
  [monoid : Monoid carrier]
  [topology : TopologicalSpace carrier]
  [continuousMul : ContinuousMul carrier]

attribute [instance] TopologicalMonoidPresentation.monoid
attribute [instance] TopologicalMonoidPresentation.topology
attribute [instance] TopologicalMonoidPresentation.continuousMul

/-- A continuous homomorphism between packaged topological monoids. -/
structure ContinuousMonoidHom
    (M N : TopologicalMonoidPresentation.{u}) where
  hom : M.carrier →* N.carrier
  continuous : Continuous hom

namespace ContinuousMonoidHom

instance {M N : TopologicalMonoidPresentation.{u}} :
    CoeFun (ContinuousMonoidHom M N) (fun _ => M.carrier -> N.carrier) :=
  ⟨fun f => f.hom⟩

/-- Composition of continuous monoid homomorphisms. -/
def comp {M N P : TopologicalMonoidPresentation.{u}}
    (f : ContinuousMonoidHom M N)
    (g : ContinuousMonoidHom N P) :
    ContinuousMonoidHom M P where
  hom := g.hom.comp f.hom
  continuous := g.continuous.comp f.continuous

/-- Identity continuous monoid homomorphism. -/
def id (M : TopologicalMonoidPresentation.{u}) :
    ContinuousMonoidHom M M where
  hom := MonoidHom.id M.carrier
  continuous := continuous_id

@[ext]
theorem ext {M N : TopologicalMonoidPresentation.{u}}
    (f g : ContinuousMonoidHom M N)
    (hom_eq : f.hom = g.hom) :
    f = g := by
  cases f
  cases g
  cases hom_eq
  rfl

/-- A continuous monoid homomorphism admitting a continuous two-sided inverse. -/
def IsIsomorphism {M N : TopologicalMonoidPresentation.{u}}
    (f : ContinuousMonoidHom M N) : Prop :=
  ∃ inverse : ContinuousMonoidHom N M,
    Function.LeftInverse inverse f ∧
      Function.RightInverse inverse f

theorem isIsomorphism_id
    (M : TopologicalMonoidPresentation.{u}) :
    IsIsomorphism (id M) :=
  ⟨id M, fun _ => rfl, fun _ => rfl⟩

theorem IsIsomorphism.comp
    {M N P : TopologicalMonoidPresentation.{u}}
    {f : ContinuousMonoidHom M N}
    {g : ContinuousMonoidHom N P}
    (hf : IsIsomorphism f) (hg : IsIsomorphism g) :
    IsIsomorphism (f.comp g) := by
  rcases hf with ⟨fInverse, hfLeft, hfRight⟩
  rcases hg with ⟨gInverse, hgLeft, hgRight⟩
  refine ⟨gInverse.comp fInverse, ?_, ?_⟩
  · intro value
    change
      fInverse (gInverse (g (f value))) = value
    rw [hgLeft, hfLeft]
  · intro value
    change
      g (f (fInverse (gInverse value))) = value
    rw [hfRight, hgRight]

end ContinuousMonoidHom

/-- An isomorphism of topological monoids. -/
structure TopologicalMonoidIso
    (M N : TopologicalMonoidPresentation.{u}) where
  toHom : ContinuousMonoidHom M N
  invHom : ContinuousMonoidHom N M
  left_inv : Function.LeftInverse invHom toHom
  right_inv : Function.RightInverse invHom toHom

namespace TopologicalMonoidIso

/-- Identity isomorphism of a packaged topological monoid. -/
def refl (M : TopologicalMonoidPresentation.{u}) :
    TopologicalMonoidIso M M where
  toHom := ContinuousMonoidHom.id M
  invHom := ContinuousMonoidHom.id M
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reverse an isomorphism of topological monoids. -/
def symm {M N : TopologicalMonoidPresentation.{u}}
    (e : TopologicalMonoidIso M N) :
    TopologicalMonoidIso N M where
  toHom := e.invHom
  invHom := e.toHom
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- Compose isomorphisms of topological monoids. -/
def trans {M N P : TopologicalMonoidPresentation.{u}}
    (e : TopologicalMonoidIso M N)
    (f : TopologicalMonoidIso N P) :
    TopologicalMonoidIso M P where
  toHom := e.toHom.comp f.toHom
  invHom := f.invHom.comp e.invHom
  left_inv x := by
    change e.invHom (f.invHom (f.toHom (e.toHom x))) = x
    rw [f.left_inv, e.left_inv]
  right_inv x := by
    change f.toHom (e.toHom (e.invHom (f.invHom x))) = x
    rw [e.right_inv, f.right_inv]

end TopologicalMonoidIso

/-- Product of packaged topological monoids. -/
def TopologicalMonoidPresentation.prod
    (M N : TopologicalMonoidPresentation.{u}) :
    TopologicalMonoidPresentation.{u} where
  carrier := M.carrier × N.carrier

/--
An object of the category `TM^tilde` used in IUT I, Example 3.4(ii).

The compact factor maps precisely onto the units of the total monoid, the
second factor is the distinguished noncompact submonoid, and multiplication
is an isomorphism of topological monoids from their product onto the total
monoid.
-/
structure SplitTopologicalMonoidPresentation where
  total : TopologicalMonoidPresentation.{u}
  compactFactor : TopologicalMonoidPresentation.{u}
  noncompactFactor : TopologicalMonoidPresentation.{u}
  compactInclusion :
    ContinuousMonoidHom compactFactor total
  noncompactInclusion :
    ContinuousMonoidHom noncompactFactor total
  compact_isUnit :
    ∀ value, IsUnit (compactInclusion value)
  every_unit_compact :
    ∀ value : total.carrier,
      IsUnit value ->
        ∃ compact : compactFactor.carrier,
          compactInclusion compact = value
  factorization :
    TopologicalMonoidIso
      (TopologicalMonoidPresentation.prod
        compactFactor noncompactFactor)
      total
  factorization_eq :
    ∀ compact noncompact,
      factorization.toHom (compact, noncompact) =
        compactInclusion compact *
          noncompactInclusion noncompact

/--
The triple occurring at an archimedean place of an `F^tilde`-prime-strip in
IUT I, Definition 5.2(ii)(b).

The selected Definition 2.3 splitting is tied to the distinguished
noncompact factor of the `TM^tilde` object through an actual equivalence of
the reconstructed rational-function monoid at an isotropic reference object.
-/
structure ArchimedeanSplitFrobenioidPresentation where
  frobenioid : SplitFrobenioidPresentation.{u}
  selectedSplitting : frobenioid.splittingIndex
  topologicalSplitting :
    SplitTopologicalMonoidPresentation.{u}
  referenceObject : frobenioid.frobenioid.carrier
  referenceObject_isotropic :
    frobenioid.frobenioid.preFrobenioid.IsIsotropic
      referenceObject
  rationalTotalIso :
    frobenioid.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
        referenceObject ≃*
      topologicalSplitting.total.carrier
  characteristic_eq_noncompactImage :
    ∀ value :
      frobenioid.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
        referenceObject,
      value ∈
          (frobenioid.splitting selectedSplitting).tau
            { obj := referenceObject
              isotropic := referenceObject_isotropic } ↔
        rationalTotalIso value ∈
          Set.range topologicalSplitting.noncompactInclusion

/--
The categorical and topological content retained from an Aut-holomorphic
orbispace.

The action is by actual autoequivalences of the underlying category.  The
analytic reconstruction theorem from Absolute Anabelian Topics III remains a
separate source obligation.
-/
structure AutHolomorphicOrbispacePresentation where
  underlying : CategoryTheory.Cat.{u, u}
  automorphisms : TopologicalMonoidPresentation.{u}
  action :
    automorphisms.carrier ->
      CategoryTheory.Equivalence underlying underlying
  action_one_functor :
    (action 1).functor = 𝟭 underlying
  action_mul_functor :
    ∀ a b,
      (action (a * b)).functor =
        (action b).functor ⋙ (action a).functor

/-- An isomorphism of the packaged Aut-holomorphic orbispace data. -/
structure AutHolomorphicOrbispaceIso
    (X Y : AutHolomorphicOrbispacePresentation.{u}) where
  underlying :
    CategoryTheory.Equivalence X.underlying Y.underlying
  automorphisms :
    TopologicalMonoidIso X.automorphisms Y.automorphisms
  action_compatible :
    ∀ a,
      (X.action a).functor ⋙ underlying.functor =
        underlying.functor ⋙
      (Y.action (automorphisms.toHom a)).functor

/-- An equivariant morphism of the Aut-holomorphic-orbispace presentations. -/
structure AutHolomorphicOrbispaceHom
    (X Y : AutHolomorphicOrbispacePresentation.{u}) where
  underlying : X.underlying ⥤ Y.underlying
  automorphisms :
    ContinuousMonoidHom X.automorphisms Y.automorphisms
  action_compatible :
    ∀ a,
      (X.action a).functor ⋙ underlying =
        underlying ⋙
          (Y.action (automorphisms a)).functor

namespace AutHolomorphicOrbispaceHom

variable {X Y Z : AutHolomorphicOrbispacePresentation.{u}}

@[ext]
theorem ext (f g : AutHolomorphicOrbispaceHom X Y)
    (underlying_eq : f.underlying = g.underlying)
    (automorphisms_eq : f.automorphisms = g.automorphisms) :
    f = g := by
  cases f
  cases g
  cases underlying_eq
  cases automorphisms_eq
  rfl

/-- Identity equivariant morphism. -/
def id (X : AutHolomorphicOrbispacePresentation.{u}) :
    AutHolomorphicOrbispaceHom X X where
  underlying := 𝟭 X.underlying
  automorphisms := ContinuousMonoidHom.id X.automorphisms
  action_compatible a := by
    change
      (X.action a).functor ⋙ 𝟭 X.underlying =
        𝟭 X.underlying ⋙ (X.action a).functor
    exact (Functor.comp_id _).trans (Functor.id_comp _).symm

/-- Composition of equivariant morphisms. -/
def comp
    (f : AutHolomorphicOrbispaceHom X Y)
    (g : AutHolomorphicOrbispaceHom Y Z) :
    AutHolomorphicOrbispaceHom X Z where
  underlying := f.underlying ⋙ g.underlying
  automorphisms := f.automorphisms.comp g.automorphisms
  action_compatible a := by
    change
      ((X.action a).functor ⋙ f.underlying) ⋙ g.underlying =
        (f.underlying ⋙ g.underlying) ⋙
          (Z.action (g.automorphisms (f.automorphisms a))).functor
    rw [f.action_compatible]
    rw [Functor.assoc]
    rw [g.action_compatible]
    rw [← Functor.assoc]

end AutHolomorphicOrbispaceHom

instance : Category AutHolomorphicOrbispacePresentation where
  Hom := AutHolomorphicOrbispaceHom
  id := AutHolomorphicOrbispaceHom.id
  comp := AutHolomorphicOrbispaceHom.comp
  id_comp f := by
    apply AutHolomorphicOrbispaceHom.ext
    · exact Functor.id_comp f.underlying
    · apply ContinuousMonoidHom.ext
      ext
      rfl
  comp_id f := by
    apply AutHolomorphicOrbispaceHom.ext
    · exact Functor.comp_id f.underlying
    · apply ContinuousMonoidHom.ext
      ext
      rfl
  assoc f g h := by
    apply AutHolomorphicOrbispaceHom.ext
    · exact Functor.assoc f.underlying g.underlying h.underlying
    · apply ContinuousMonoidHom.ext
      ext
      rfl

/--
An equivariant Aut-holomorphic-orbispace morphism is an isomorphism when its
underlying functor is an equivalence and its automorphism homomorphism has a
continuous inverse.
-/
def AutHolomorphicOrbispaceHom.IsIsomorphism
    {X Y : AutHolomorphicOrbispacePresentation.{u}}
    (f : AutHolomorphicOrbispaceHom X Y) : Prop :=
  f.underlying.IsEquivalence ∧
    f.automorphisms.IsIsomorphism

theorem AutHolomorphicOrbispaceHom.isIsomorphism_id
    (X : AutHolomorphicOrbispacePresentation.{u}) :
    (𝟙 X : X ⟶ X).IsIsomorphism := by
  constructor
  · change (𝟭 X.underlying).IsEquivalence
    infer_instance
  · exact ContinuousMonoidHom.isIsomorphism_id X.automorphisms

theorem AutHolomorphicOrbispaceHom.IsIsomorphism.comp
    {X Y Z : AutHolomorphicOrbispacePresentation.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : f.IsIsomorphism) (hg : g.IsIsomorphism) :
    (f ≫ g).IsIsomorphism := by
  constructor
  · change (f.underlying ⋙ g.underlying).IsEquivalence
    letI : f.underlying.IsEquivalence := hf.1
    letI : g.underlying.IsEquivalence := hg.1
    infer_instance
  · exact hf.2.comp hg.2

/-- The selected nonarchimedean places of source-native initial theta data. -/
def SourceSelectedFinitePlace
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : SourceInitialThetaCore Fmod F K) :=
  {v : NumberField.FinitePlace K // v ∈ theta.valuations.selected}

/-- The selected archimedean places of source-native initial theta data. -/
def SourceSelectedInfinitePlace
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : SourceInitialThetaCore Fmod F K) :=
  {v : NumberField.InfinitePlace K //
    v ∈ theta.valuations.selectedInfinite}

/--
The nonarchimedean local model required by IUT I, Definition 3.6(a).

The five derived categories are the objects denoted
`D_v`, `Dtilde_v`, `DTheta_v`, `Ftilde_v`, and `FTheta_v` in the source.
Their derivation from the category alone is intentionally retained as a
separate certificate instead of being replaced by fresh identifiers.
-/
structure IUTINonarchimedeanLocalModel
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : SourceInitialThetaCore Fmod F K)
    (v : SourceSelectedFinitePlace theta) where
  frobenioid : FrobenioidPresentation.{u}
  d : CategoryTheory.Cat.{u, u}
  dTilde : CategoryTheory.Cat.{u, u}
  dTheta : CategoryTheory.Cat.{u, u}
  fTilde : CategoryTheory.Cat.{u, u}
  fTheta : CategoryTheory.Cat.{u, u}
  fTildeSplit : SplitFrobenioidPresentation.{u}
  fThetaSplit : SplitFrobenioidPresentation.{u}
  fTildeSplitCarrier :
    CategoryTheory.Equivalence
      fTildeSplit.frobenioid.carrier fTilde
  fThetaSplitCarrier :
    CategoryTheory.Equivalence
      fThetaSplit.frobenioid.carrier fTheta
  unitsTilde : TopologicalMonoidPresentation.{u}
  unitsTheta : TopologicalMonoidPresentation.{u}
  unitsTautological :
    TopologicalMonoidIso unitsTilde unitsTheta
  baseDerivedFromCategory :
    CategoryTheory.Equivalence
      frobenioid.baseCategory d
  derivedFromCategory :
    CategoryTheory.Equivalence frobenioid.carrier d
  localOrbicurveGroup :
    EtaleFundamentalGroup
  localOrbicurveGroup_eq :
    localOrbicurveGroup =
      (theta.finiteLocalCores v.1).orbicurves.xFundamentalGroups.arithmetic.toEtaleFundamentalGroup

namespace IUTINonarchimedeanLocalModel

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : SourceInitialThetaCore Fmod F K}
variable {v : SourceSelectedFinitePlace theta}

/-- The reconstructed `C_v` arithmetic fundamental group of Definition 5.2(v). -/
noncomputable abbrev coreFundamentalGroup
    (_model : IUTINonarchimedeanLocalModel theta v) :
    ProfiniteGrp.{u} :=
  (theta.finiteLocalCores v.1).orbicurves.cFundamentalGroups.arithmetic.group

/--
The natural open immersion from the fundamental group represented by `D_v`,
namely the group of the local `X_v`, into the reconstructed `C_v` group.
-/
noncomputable def dToCoreOpenEmbedding
    (model : IUTINonarchimedeanLocalModel theta v) :
    ProfiniteOpenEmbedding
      model.localOrbicurveGroup.group model.coreFundamentalGroup := by
  rw [model.localOrbicurveGroup_eq]
  exact
    ((theta.finiteLocalCores v.1).orbicurves).fundamentalGroupInclusion.arithmetic

/-- The `D_v -> C_v` map is injective on arithmetic fundamental groups. -/
theorem dToCore_injective
    (model : IUTINonarchimedeanLocalModel theta v) :
    Function.Injective model.dToCoreOpenEmbedding.hom :=
  model.dToCoreOpenEmbedding.injective

/-- The image of the `D_v -> C_v` fundamental-group map is open. -/
theorem dToCore_open_range
    (model : IUTINonarchimedeanLocalModel theta v) :
    IsOpen (Set.range model.dToCoreOpenEmbedding.hom) :=
  model.dToCoreOpenEmbedding.open_range

end IUTINonarchimedeanLocalModel

/--
The archimedean local model required by IUT I, Definition 3.6(b).

`kummer` is a continuous injective monoid homomorphism, rather than an
uninterpreted relation between the category and its Aut-holomorphic orbispace.
-/
structure IUTIArchimedeanLocalModel
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : SourceInitialThetaCore Fmod F K)
    (_v : SourceSelectedInfinitePlace theta) where
  c : CategoryTheory.Cat.{u, u}
  d : AutHolomorphicOrbispacePresentation.{u}
  units : TopologicalMonoidPresentation.{u}
  kummer : ContinuousMonoidHom units d.automorphisms
  kummer_injective : Function.Injective kummer
  dTilde : AutHolomorphicOrbispacePresentation.{u}
  dTheta : AutHolomorphicOrbispacePresentation.{u}
  fTilde : CategoryTheory.Cat.{u, u}
  fTheta : CategoryTheory.Cat.{u, u}
  fTildeMonoAnalytic :
    ArchimedeanSplitFrobenioidPresentation.{u}
  fThetaMonoAnalytic :
    ArchimedeanSplitFrobenioidPresentation.{u}
  fTildeSplitCarrier :
    CategoryTheory.Equivalence
      fTildeMonoAnalytic.frobenioid.frobenioid.carrier fTilde
  fThetaSplitCarrier :
    CategoryTheory.Equivalence
      fThetaMonoAnalytic.frobenioid.frobenioid.carrier fTheta
  unitsTilde : TopologicalMonoidPresentation.{u}
  unitsTheta : TopologicalMonoidPresentation.{u}
  fTildeTotalIso :
    TopologicalMonoidIso
      unitsTilde fTildeMonoAnalytic.topologicalSplitting.total
  fThetaTotalIso :
    TopologicalMonoidIso
      unitsTheta fThetaMonoAnalytic.topologicalSplitting.total
  unitsTautological :
    TopologicalMonoidIso unitsTilde unitsTheta

/--
The global model collection required by IUT I, Definition 3.6(c).

The prime-to-place correspondence and every local currency-exchange map
`rho_v` are typed bijections/isomorphisms.  Constructing `Prime` from the
category, as in Frobenioids I, Theorem 6.4(iii), remains an explicit missing
theorem and is not simulated by an arbitrary predicate.
-/
structure IUTIGlobalFrobenioidModel
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : SourceInitialThetaCore Fmod F K) where
  frobenioid : FrobenioidPresentation.{u}
  Prime : Type u
  primeEquivSelectedPlace :
    Prime ≃
      {v : ThetaPlace K // v ∈ theta.valuations.selectedPlaces}
  characteristicLocal :
    (v : {v : ThetaPlace K // v ∈ theta.valuations.selectedPlaces}) ->
      TopologicalMonoidPresentation.{u}
  realifiedLocal :
    (v : {v : ThetaPlace K // v ∈ theta.valuations.selectedPlaces}) ->
      TopologicalMonoidPresentation.{u}
  rho :
    ∀ v, TopologicalMonoidIso (characteristicLocal v) (realifiedLocal v)
  thetaGlobal : FrobenioidPresentation.{u}
  dGlobal : FrobenioidPresentation.{u}
  modToTheta :
    CategoryTheory.Equivalence
      frobenioid.carrier thetaGlobal.carrier
  modToD :
    CategoryTheory.Equivalence
      frobenioid.carrier dGlobal.carrier

/--
The canonical local/global models cited by IUT I, Examples 3.2-3.5.

Constructing this record from `theta` is a named source obligation.  In
particular, this module provides no default, choice-based, or toy constructor.
-/
structure IUTIThetaHodgeTheaterModels
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : SourceInitialThetaCore Fmod F K) where
  nonarchimedean :
    ∀ v : SourceSelectedFinitePlace theta,
      IUTINonarchimedeanLocalModel theta v
  archimedean :
    ∀ v : SourceSelectedInfinitePlace theta,
      IUTIArchimedeanLocalModel theta v
  global : IUTIGlobalFrobenioidModel theta

/--
A holomorphic base-prime-strip from IUT I, Definition 4.1(i)-(ii).

The local objects are tied by equivalences to the Definition 3.6 models.  The
label-class fibers are tied to the actual nonzero `l`-torsion labels modulo
inversion, with the distinguished class fixed to the canonical Tate generator.
-/
structure SourceDPrimeStrip
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
  history : SourceThetaArithmeticHistory theta
  nonarchimedean :
    SourceSelectedFinitePlace theta ->
      CategoryTheory.Cat.{u, u}
  nonarchimedeanEquivalence :
    ∀ v,
      CategoryTheory.Equivalence
        (nonarchimedean v) (models.nonarchimedean v).d
  archimedean :
    SourceSelectedInfinitePlace theta ->
      AutHolomorphicOrbispacePresentation.{u}
  archimedeanIso :
    ∀ v,
      AutHolomorphicOrbispaceIso
        (archimedean v) (models.archimedean v).d
  labelClasses :
    (v : {v : ThetaPlace K // v ∈ theta.valuations.selectedPlaces}) ->
      Type u
  labelEquiv :
    ∀ v,
      labelClasses v ≃
        EtaleTheta.SignLabel (EtaleTheta.LTorsionLabel theta.l.value)
  canonicalLabelClass :
    ∀ v, labelClasses v
  canonicalLabelClass_eq :
    ∀ v,
      labelEquiv v (canonicalLabelClass v) =
      EtaleTheta.canonicalTateSignLabel theta.l.value
          (lt_of_lt_of_le (by decide : 1 < 5) theta.l.ge_five)

/--
A morphism of holomorphic D-prime-strips, as in IUT I, Definition 4.1(iv):
one constituent morphism at every place.
-/
structure SourceDPrimeStripHom
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
    (source target : SourceDPrimeStrip models) where
  nonarchimedean :
    ∀ v, source.nonarchimedean v ⥤ target.nonarchimedean v
  archimedean :
    ∀ v, source.archimedean v ⟶ target.archimedean v

namespace SourceDPrimeStripHom

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : SourceInitialThetaCore Fmod F K}
variable {models : IUTIThetaHodgeTheaterModels theta}
variable {source target third : SourceDPrimeStrip models}

@[ext]
theorem ext (f g : SourceDPrimeStripHom source target)
    (nonarchimedean_eq :
      f.nonarchimedean = g.nonarchimedean)
    (archimedean_eq :
      f.archimedean = g.archimedean) :
    f = g := by
  cases f
  cases g
  cases nonarchimedean_eq
  cases archimedean_eq
  rfl

/-- Identity placewise morphism. -/
def id (source : SourceDPrimeStrip models) :
    SourceDPrimeStripHom source source where
  nonarchimedean v := 𝟭 (source.nonarchimedean v)
  archimedean v := 𝟙 (source.archimedean v)

/-- Composition of placewise morphisms. -/
def comp
    (f : SourceDPrimeStripHom source target)
    (g : SourceDPrimeStripHom target third) :
    SourceDPrimeStripHom source third where
  nonarchimedean v :=
    f.nonarchimedean v ⋙ g.nonarchimedean v
  archimedean v :=
    f.archimedean v ≫ g.archimedean v

end SourceDPrimeStripHom

instance
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta} :
    Category (SourceDPrimeStrip models) where
  Hom := SourceDPrimeStripHom
  id := SourceDPrimeStripHom.id
  comp := SourceDPrimeStripHom.comp
  id_comp f := by
    apply SourceDPrimeStripHom.ext
    · funext v
      exact Functor.id_comp (f.nonarchimedean v)
    · funext v
      exact Category.id_comp (f.archimedean v)
  comp_id f := by
    apply SourceDPrimeStripHom.ext
    · funext v
      exact Functor.comp_id (f.nonarchimedean v)
    · funext v
      exact Category.comp_id (f.archimedean v)
  assoc f g h := by
    apply SourceDPrimeStripHom.ext
    · funext v
      exact Functor.assoc
        (f.nonarchimedean v)
        (g.nonarchimedean v)
        (h.nonarchimedean v)
    · funext v
      exact Category.assoc
        (f.archimedean v)
        (g.archimedean v)
        (h.archimedean v)

/--
A mono-analytic D-prime-strip from IUT I, Definition 4.1(iii).
-/
structure SourceDMonoAnalyticPrimeStrip
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
  nonarchimedean :
    SourceSelectedFinitePlace theta ->
      CategoryTheory.Cat.{u, u}
  nonarchimedeanEquivalence :
    ∀ v,
      CategoryTheory.Equivalence
        (nonarchimedean v) (models.nonarchimedean v).dTilde
  archimedean :
    SourceSelectedInfinitePlace theta ->
      AutHolomorphicOrbispacePresentation.{u}
  archimedeanIso :
    ∀ v,
      AutHolomorphicOrbispaceIso
        (archimedean v) (models.archimedean v).dTilde

/-- A placewise morphism of mono-analytic D-prime-strips. -/
structure SourceDMonoAnalyticPrimeStripHom
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
    (source target : SourceDMonoAnalyticPrimeStrip models) where
  nonarchimedean :
    ∀ v, source.nonarchimedean v ⥤ target.nonarchimedean v
  archimedean :
    ∀ v, source.archimedean v ⟶ target.archimedean v

namespace SourceDMonoAnalyticPrimeStripHom

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : SourceInitialThetaCore Fmod F K}
variable {models : IUTIThetaHodgeTheaterModels theta}
variable
  {source target third : SourceDMonoAnalyticPrimeStrip models}

@[ext]
theorem ext
    (f g : SourceDMonoAnalyticPrimeStripHom source target)
    (nonarchimedean_eq :
      f.nonarchimedean = g.nonarchimedean)
    (archimedean_eq :
      f.archimedean = g.archimedean) :
    f = g := by
  cases f
  cases g
  cases nonarchimedean_eq
  cases archimedean_eq
  rfl

def id (source : SourceDMonoAnalyticPrimeStrip models) :
    SourceDMonoAnalyticPrimeStripHom source source where
  nonarchimedean v := 𝟭 (source.nonarchimedean v)
  archimedean v := 𝟙 (source.archimedean v)

def comp
    (f : SourceDMonoAnalyticPrimeStripHom source target)
    (g : SourceDMonoAnalyticPrimeStripHom target third) :
    SourceDMonoAnalyticPrimeStripHom source third where
  nonarchimedean v :=
    f.nonarchimedean v ⋙ g.nonarchimedean v
  archimedean v :=
    f.archimedean v ≫ g.archimedean v

end SourceDMonoAnalyticPrimeStripHom

instance
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta} :
    Category (SourceDMonoAnalyticPrimeStrip models) where
  Hom := SourceDMonoAnalyticPrimeStripHom
  id := SourceDMonoAnalyticPrimeStripHom.id
  comp := SourceDMonoAnalyticPrimeStripHom.comp
  id_comp f := by
    apply SourceDMonoAnalyticPrimeStripHom.ext
    · funext v
      exact Functor.id_comp (f.nonarchimedean v)
    · funext v
      exact Category.id_comp (f.archimedean v)
  comp_id f := by
    apply SourceDMonoAnalyticPrimeStripHom.ext
    · funext v
      exact Functor.comp_id (f.nonarchimedean v)
    · funext v
      exact Category.comp_id (f.archimedean v)
  assoc f g h := by
    apply SourceDMonoAnalyticPrimeStripHom.ext
    · funext v
      exact Functor.assoc
        (f.nonarchimedean v)
        (g.nonarchimedean v)
        (h.nonarchimedean v)
    · funext v
      exact Category.assoc
        (f.archimedean v)
        (g.archimedean v)
        (h.archimedean v)

/--
The natural mono-analyticization operation of Definition 4.1(iv).

The inclusions back into the holomorphic strip and their naturality prevent
this operation from being merely an unrelated object assignment.
-/
structure SourceDMonoAnalyticization
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
  functor :
    CategoryTheory.Cat.of (SourceDPrimeStrip models) ⥤
      CategoryTheory.Cat.of
        (SourceDMonoAnalyticPrimeStrip models)
  nonarchimedeanInclusion :
    ∀ (strip : SourceDPrimeStrip models) v,
      (functor.obj strip).nonarchimedean v ⥤
        strip.nonarchimedean v
  nonarchimedeanInclusion_fullyFaithful :
    ∀ strip v,
      (nonarchimedeanInclusion strip v).FullyFaithful
  archimedeanMap :
    ∀ (strip : SourceDPrimeStrip models) v,
      (functor.obj strip).archimedean v ⟶
        strip.archimedean v
  nonarchimedean_naturality :
    ∀ {source target : SourceDPrimeStrip models}
      (f : source ⟶ target) v,
      (functor.map f).nonarchimedean v ⋙
          nonarchimedeanInclusion target v =
        nonarchimedeanInclusion source v ⋙
          f.nonarchimedean v
  archimedean_naturality :
    ∀ {source target : SourceDPrimeStrip models}
      (f : source ⟶ target) v,
      (functor.map f).archimedean v ≫
          archimedeanMap target v =
        archimedeanMap source v ≫
          f.archimedean v

/--
A holomorphic Frobenioid-prime-strip from IUT I, Definition 5.2(i).

At finite places the strip carries a packaged Frobenioid, not just its
degree set.  At infinite places the complete category/orbispace/Kummer
collection is retained.
-/
structure SourceFPrimeStrip
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
  history : SourceThetaArithmeticHistory theta
  nonarchimedean :
    SourceSelectedFinitePlace theta ->
      FrobenioidPresentation.{u}
  nonarchimedeanEquivalence :
    ∀ v,
      CategoryTheory.Equivalence
        (nonarchimedean v).carrier
        (models.nonarchimedean v).frobenioid.carrier
  nonarchimedeanBaseEquivalence :
    ∀ v,
      CategoryTheory.Equivalence
        (nonarchimedean v).baseCategory
        (models.nonarchimedean v).d
  archimedean :
    ∀ v : SourceSelectedInfinitePlace theta,
      IUTIArchimedeanLocalModel theta v
  archimedeanCategoryEquivalence :
    ∀ v,
      CategoryTheory.Equivalence
        (archimedean v).c (models.archimedean v).c
  archimedeanOrbispaceIso :
    ∀ v,
      AutHolomorphicOrbispaceIso
        (archimedean v).d (models.archimedean v).d
  archimedeanUnitIso :
    ∀ v,
      TopologicalMonoidIso
        (archimedean v).units (models.archimedean v).units
  kummer_compatible :
    ∀ v x,
      (models.archimedean v).kummer
          ((archimedeanUnitIso v).toHom x) =
        (archimedeanOrbispaceIso v).automorphisms.toHom
          ((archimedean v).kummer x)

/--
An isomorphism between the complete archimedean collections
`(C_v, D_v, kappa_v)` of Definition 5.2(i)(b), presented by its forward maps
and proofs that all three maps are isomorphisms.
-/
structure SourceFPrimeStripArchHom
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {v : SourceSelectedInfinitePlace theta}
    (source target : IUTIArchimedeanLocalModel theta v) where
  category : source.c ⥤ target.c
  category_isEquivalence : category.IsEquivalence
  orbispace : source.d ⟶ target.d
  orbispace_isIsomorphism :
    orbispace.IsIsomorphism
  units :
    ContinuousMonoidHom source.units target.units
  units_isIsomorphism :
    units.IsIsomorphism
  kummer_compatible :
    ∀ value,
      target.kummer (units value) =
        orbispace.automorphisms
          (source.kummer value)

namespace SourceFPrimeStripArchHom

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
    {v : SourceSelectedInfinitePlace theta}
    {source middle target : IUTIArchimedeanLocalModel theta v}

@[ext]
theorem ext
    (f g : SourceFPrimeStripArchHom source target)
    (category_eq : f.category = g.category)
    (orbispace_eq : f.orbispace = g.orbispace)
    (units_eq : f.units = g.units) :
    f = g := by
  cases f
  cases g
  cases category_eq
  cases orbispace_eq
  cases units_eq
  rfl

/-- Identity isomorphism of an archimedean F-component. -/
def id (source : IUTIArchimedeanLocalModel theta v) :
    SourceFPrimeStripArchHom source source where
  category := 𝟭 source.c
  category_isEquivalence := by infer_instance
  orbispace := 𝟙 source.d
  orbispace_isIsomorphism :=
    AutHolomorphicOrbispaceHom.isIsomorphism_id source.d
  units := ContinuousMonoidHom.id source.units
  units_isIsomorphism :=
    ContinuousMonoidHom.isIsomorphism_id source.units
  kummer_compatible _ := rfl

/-- Composition of archimedean F-component isomorphisms. -/
def comp
    (f : SourceFPrimeStripArchHom source middle)
    (g : SourceFPrimeStripArchHom middle target) :
    SourceFPrimeStripArchHom source target where
  category := f.category ⋙ g.category
  category_isEquivalence := by
    letI : f.category.IsEquivalence := f.category_isEquivalence
    letI : g.category.IsEquivalence := g.category_isEquivalence
    infer_instance
  orbispace := f.orbispace ≫ g.orbispace
  orbispace_isIsomorphism :=
    f.orbispace_isIsomorphism.comp
      g.orbispace_isIsomorphism
  units := f.units.comp g.units
  units_isIsomorphism :=
    f.units_isIsomorphism.comp g.units_isIsomorphism
  kummer_compatible value := by
    change
      target.kummer (g.units (f.units value)) =
        g.orbispace.automorphisms
          (f.orbispace.automorphisms
            (source.kummer value))
    rw [g.kummer_compatible, f.kummer_compatible]

end SourceFPrimeStripArchHom

instance
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {v : SourceSelectedInfinitePlace theta} :
    Category (IUTIArchimedeanLocalModel theta v) where
  Hom := SourceFPrimeStripArchHom
  id := SourceFPrimeStripArchHom.id
  comp := SourceFPrimeStripArchHom.comp
  id_comp f := by
    apply SourceFPrimeStripArchHom.ext
    · exact Functor.id_comp f.category
    · exact Category.id_comp f.orbispace
    · apply ContinuousMonoidHom.ext
      rfl
  comp_id f := by
    apply SourceFPrimeStripArchHom.ext
    · exact Functor.comp_id f.category
    · exact Category.comp_id f.orbispace
    · apply ContinuousMonoidHom.ext
      rfl
  assoc f g h := by
    apply SourceFPrimeStripArchHom.ext
    · exact Functor.assoc f.category g.category h.category
    · exact Category.assoc f.orbispace g.orbispace h.orbispace
    · apply ContinuousMonoidHom.ext
      rfl

/--
A morphism of holomorphic F-prime-strips in IUT I, Definition 5.2(iii).
Every finite component is required to be an equivalence, and every infinite
component is an isomorphism of the complete Kummer collection.
-/
structure SourceFPrimeStripHom
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
    (source target : SourceFPrimeStrip models) where
  nonarchimedean :
    ∀ v,
      (source.nonarchimedean v).carrier ⥤
        (target.nonarchimedean v).carrier
  nonarchimedean_isEquivalence :
    ∀ v, (nonarchimedean v).IsEquivalence
  nonarchimedeanBase :
    ∀ v,
      (source.nonarchimedean v).baseCategory ⥤
        (target.nonarchimedean v).baseCategory
  nonarchimedeanBase_isEquivalence :
    ∀ v, (nonarchimedeanBase v).IsEquivalence
  nonarchimedeanBase_compatible :
    ∀ v,
      (source.nonarchimedean v).preFrobenioid.base ⋙
          nonarchimedeanBase v =
        nonarchimedean v ⋙
          (target.nonarchimedean v).preFrobenioid.base
  archimedean :
    ∀ v, source.archimedean v ⟶ target.archimedean v

namespace SourceFPrimeStripHom

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
    {source middle target : SourceFPrimeStrip models}

@[ext]
theorem ext
    (f g : SourceFPrimeStripHom source target)
    (nonarchimedean_eq :
      f.nonarchimedean = g.nonarchimedean)
    (nonarchimedeanBase_eq :
      f.nonarchimedeanBase = g.nonarchimedeanBase)
    (archimedean_eq :
      f.archimedean = g.archimedean) :
    f = g := by
  cases f
  cases g
  cases nonarchimedean_eq
  cases nonarchimedeanBase_eq
  cases archimedean_eq
  rfl

/-- Identity F-prime-strip morphism. -/
def id (source : SourceFPrimeStrip models) :
    SourceFPrimeStripHom source source where
  nonarchimedean _ := 𝟭 _
  nonarchimedean_isEquivalence _ := by infer_instance
  nonarchimedeanBase _ := 𝟭 _
  nonarchimedeanBase_isEquivalence _ := by infer_instance
  nonarchimedeanBase_compatible v :=
    (Functor.comp_id
      (source.nonarchimedean v).preFrobenioid.base).trans
      (Functor.id_comp
        (source.nonarchimedean v).preFrobenioid.base).symm
  archimedean _ := 𝟙 _

/-- Composition of F-prime-strip morphisms. -/
def comp
    (f : SourceFPrimeStripHom source middle)
    (g : SourceFPrimeStripHom middle target) :
    SourceFPrimeStripHom source target where
  nonarchimedean v :=
    f.nonarchimedean v ⋙ g.nonarchimedean v
  nonarchimedean_isEquivalence v := by
    letI : (f.nonarchimedean v).IsEquivalence :=
      f.nonarchimedean_isEquivalence v
    letI : (g.nonarchimedean v).IsEquivalence :=
      g.nonarchimedean_isEquivalence v
    infer_instance
  nonarchimedeanBase v :=
    f.nonarchimedeanBase v ⋙
      g.nonarchimedeanBase v
  nonarchimedeanBase_isEquivalence v := by
    letI : (f.nonarchimedeanBase v).IsEquivalence :=
      f.nonarchimedeanBase_isEquivalence v
    letI : (g.nonarchimedeanBase v).IsEquivalence :=
      g.nonarchimedeanBase_isEquivalence v
    infer_instance
  nonarchimedeanBase_compatible v := by
    rw [← Functor.assoc]
    rw [f.nonarchimedeanBase_compatible]
    rw [Functor.assoc]
    rw [g.nonarchimedeanBase_compatible]
    rw [← Functor.assoc]
  archimedean v :=
    f.archimedean v ≫ g.archimedean v

end SourceFPrimeStripHom

instance
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta} :
    Category (SourceFPrimeStrip models) where
  Hom := SourceFPrimeStripHom
  id := SourceFPrimeStripHom.id
  comp := SourceFPrimeStripHom.comp
  id_comp f := by
    apply SourceFPrimeStripHom.ext
    · funext v
      exact Functor.id_comp (f.nonarchimedean v)
    · funext v
      exact Functor.id_comp (f.nonarchimedeanBase v)
    · funext v
      exact Category.id_comp (f.archimedean v)
  comp_id f := by
    apply SourceFPrimeStripHom.ext
    · funext v
      exact Functor.comp_id (f.nonarchimedean v)
    · funext v
      exact Functor.comp_id (f.nonarchimedeanBase v)
    · funext v
      exact Category.comp_id (f.archimedean v)
  assoc f g h := by
    apply SourceFPrimeStripHom.ext
    · funext v
      exact
        Functor.assoc
          (f.nonarchimedean v)
          (g.nonarchimedean v)
          (h.nonarchimedean v)
    · funext v
      exact
        Functor.assoc
          (f.nonarchimedeanBase v)
          (g.nonarchimedeanBase v)
          (h.nonarchimedeanBase v)
    · funext v
      exact
        Category.assoc
          (f.archimedean v)
          (g.archimedean v)
          (h.archimedean v)

/--
Two representatives of an isomorphism of `F`-prime-strips determine the same
map in the coarsification of IUT I, Section 0, when their categorical
components are naturally isomorphic and their noncategorical components
agree.  Proof fields and the chosen equivalence witnesses are deliberately
not part of this relation.
-/
structure SourceFPrimeStripHom.NaturallyIsomorphic
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
    {source target : SourceFPrimeStrip models}
    (first second : SourceFPrimeStripHom source target) : Prop where
  nonarchimedean :
    ∀ v, Nonempty (first.nonarchimedean v ≅ second.nonarchimedean v)
  nonarchimedeanBase :
    ∀ v, Nonempty
      (first.nonarchimedeanBase v ≅ second.nonarchimedeanBase v)
  archimedeanCategory :
    ∀ v, Nonempty ((first.archimedean v).category ≅
      (second.archimedean v).category)
  archimedeanOrbispace :
    ∀ v, (first.archimedean v).orbispace =
      (second.archimedean v).orbispace
  archimedeanUnits :
    ∀ v, (first.archimedean v).units =
      (second.archimedean v).units

namespace SourceFPrimeStripHom.NaturallyIsomorphic

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
    {source middle target : SourceFPrimeStrip models}

/-- Reflexivity of the coarsified prime-strip map relation. -/
protected def refl (map : SourceFPrimeStripHom source target) :
    map.NaturallyIsomorphic map where
  nonarchimedean _ := ⟨Iso.refl _⟩
  nonarchimedeanBase _ := ⟨Iso.refl _⟩
  archimedeanCategory _ := ⟨Iso.refl _⟩
  archimedeanOrbispace _ := rfl
  archimedeanUnits _ := rfl

/-- Symmetry of the coarsified prime-strip map relation. -/
protected def symm
    {first second : SourceFPrimeStripHom source target}
    (relation : first.NaturallyIsomorphic second) :
    second.NaturallyIsomorphic first where
  nonarchimedean v :=
    (relation.nonarchimedean v).map Iso.symm
  nonarchimedeanBase v :=
    (relation.nonarchimedeanBase v).map Iso.symm
  archimedeanCategory v :=
    (relation.archimedeanCategory v).map Iso.symm
  archimedeanOrbispace v := (relation.archimedeanOrbispace v).symm
  archimedeanUnits v := (relation.archimedeanUnits v).symm

/-- Transitivity of the coarsified prime-strip map relation. -/
protected def trans
    {first second third : SourceFPrimeStripHom source target}
    (firstSecond : first.NaturallyIsomorphic second)
    (secondThird : second.NaturallyIsomorphic third) :
    first.NaturallyIsomorphic third where
  nonarchimedean v := by
    rcases firstSecond.nonarchimedean v with ⟨firstIso⟩
    rcases secondThird.nonarchimedean v with ⟨secondIso⟩
    exact ⟨firstIso.trans secondIso⟩
  nonarchimedeanBase v := by
    rcases firstSecond.nonarchimedeanBase v with ⟨firstIso⟩
    rcases secondThird.nonarchimedeanBase v with ⟨secondIso⟩
    exact ⟨firstIso.trans secondIso⟩
  archimedeanCategory v := by
    rcases firstSecond.archimedeanCategory v with ⟨firstIso⟩
    rcases secondThird.archimedeanCategory v with ⟨secondIso⟩
    exact ⟨firstIso.trans secondIso⟩
  archimedeanOrbispace v :=
    (firstSecond.archimedeanOrbispace v).trans
      (secondThird.archimedeanOrbispace v)
  archimedeanUnits v :=
    (firstSecond.archimedeanUnits v).trans
      (secondThird.archimedeanUnits v)

/-- Composition respects natural-isomorphism classes in both variables. -/
protected def comp
    {first first' : SourceFPrimeStripHom source middle}
    {second second' : SourceFPrimeStripHom middle target}
    (hFirst : first.NaturallyIsomorphic first')
    (hSecond : second.NaturallyIsomorphic second') :
    (first.comp second).NaturallyIsomorphic
      (first'.comp second') where
  nonarchimedean v := by
    rcases hFirst.nonarchimedean v with ⟨firstIso⟩
    rcases hSecond.nonarchimedean v with ⟨secondIso⟩
    exact ⟨NatIso.hcomp firstIso secondIso⟩
  nonarchimedeanBase v := by
    rcases hFirst.nonarchimedeanBase v with ⟨firstIso⟩
    rcases hSecond.nonarchimedeanBase v with ⟨secondIso⟩
    exact ⟨NatIso.hcomp firstIso secondIso⟩
  archimedeanCategory v := by
    rcases hFirst.archimedeanCategory v with ⟨firstIso⟩
    rcases hSecond.archimedeanCategory v with ⟨secondIso⟩
    exact ⟨NatIso.hcomp firstIso secondIso⟩
  archimedeanOrbispace v := by
    change
      (first.archimedean v).orbispace ≫
          (second.archimedean v).orbispace =
        (first'.archimedean v).orbispace ≫
          (second'.archimedean v).orbispace
    rw [hFirst.archimedeanOrbispace v,
      hSecond.archimedeanOrbispace v]
  archimedeanUnits v := by
    change
      (first.archimedean v).units.comp
          (second.archimedean v).units =
        (first'.archimedean v).units.comp
          (second'.archimedean v).units
    rw [hFirst.archimedeanUnits v,
      hSecond.archimedeanUnits v]

/-- Associativity holds in the coarsified prime-strip map relation. -/
protected def assoc
    (first : SourceFPrimeStripHom source middle)
    (second : SourceFPrimeStripHom middle target)
    {final : SourceFPrimeStrip models}
    (third : SourceFPrimeStripHom target final) :
    ((first.comp second).comp third).NaturallyIsomorphic
      (first.comp (second.comp third)) where
  nonarchimedean v :=
    ⟨eqToIso (Functor.assoc
      (first.nonarchimedean v)
      (second.nonarchimedean v)
      (third.nonarchimedean v))⟩
  nonarchimedeanBase v :=
    ⟨eqToIso (Functor.assoc
      (first.nonarchimedeanBase v)
      (second.nonarchimedeanBase v)
      (third.nonarchimedeanBase v))⟩
  archimedeanCategory v :=
    ⟨eqToIso (Functor.assoc
      (first.archimedean v).category
      (second.archimedean v).category
      (third.archimedean v).category)⟩
  archimedeanOrbispace v :=
    congrArg SourceFPrimeStripArchHom.orbispace
      (Category.assoc (first.archimedean v)
        (second.archimedean v) (third.archimedean v))
  archimedeanUnits v :=
    congrArg SourceFPrimeStripArchHom.units
      (Category.assoc (first.archimedean v)
        (second.archimedean v) (third.archimedean v))

end SourceFPrimeStripHom.NaturallyIsomorphic

/-- The setoid implementing the coarsification convention for `F`-strips. -/
def sourceFPrimeStripHomSetoid
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
    (source target : SourceFPrimeStrip models) :
    Setoid (SourceFPrimeStripHom source target) where
  r := SourceFPrimeStripHom.NaturallyIsomorphic
  iseqv :=
    ⟨SourceFPrimeStripHom.NaturallyIsomorphic.refl,
      SourceFPrimeStripHom.NaturallyIsomorphic.symm,
      SourceFPrimeStripHom.NaturallyIsomorphic.trans⟩

/--
The full poly-isomorphism of two `F`-prime-strips in the sense of IUT I,
Section 0: all componentwise equivalence maps, modulo natural isomorphism of
their categorical components.
-/
abbrev SourceFPrimeStripFullPolyIsomorphism
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
    (source target : SourceFPrimeStrip models) :=
  Quotient (sourceFPrimeStripHomSetoid source target)

namespace SourceFPrimeStripFullPolyIsomorphism

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
    {source middle target final : SourceFPrimeStrip models}

/-- The class represented by a componentwise equivalence map. -/
def ofHom (map : SourceFPrimeStripHom source target) :
    SourceFPrimeStripFullPolyIsomorphism source target :=
  Quotient.mk _ map

/-- The identity member of the full poly-isomorphism. -/
def id (source : SourceFPrimeStrip models) :
    SourceFPrimeStripFullPolyIsomorphism source source :=
  ofHom (SourceFPrimeStripHom.id source)

/-- Composition in the coarsified category of `F`-prime-strips. -/
def comp
    (first : SourceFPrimeStripFullPolyIsomorphism source middle)
    (second : SourceFPrimeStripFullPolyIsomorphism middle target) :
    SourceFPrimeStripFullPolyIsomorphism source target :=
  Quotient.map₂ SourceFPrimeStripHom.comp
    (by
      intro first first' hFirst second second' hSecond
      exact
        SourceFPrimeStripHom.NaturallyIsomorphic.comp hFirst hSecond)
    first second

@[simp]
theorem comp_ofHom
    (first : SourceFPrimeStripHom source middle)
    (second : SourceFPrimeStripHom middle target) :
    comp (ofHom first) (ofHom second) =
      ofHom (first.comp second) := by
  change Quotient.mk _ (first.comp second) =
    Quotient.mk _ (first.comp second)
  rfl

@[simp]
theorem id_comp
    (map : SourceFPrimeStripFullPolyIsomorphism source target) :
    comp (id source) map = map := by
  refine Quotient.inductionOn map ?_
  intro representative
  change ofHom ((𝟙 source) ≫ representative) =
    ofHom representative
  rw [Category.id_comp]

@[simp]
theorem comp_id
    (map : SourceFPrimeStripFullPolyIsomorphism source target) :
    comp map (id target) = map := by
  refine Quotient.inductionOn map ?_
  intro representative
  change ofHom (representative ≫ (𝟙 target)) =
    ofHom representative
  rw [Category.comp_id]

theorem comp_assoc
    (first : SourceFPrimeStripFullPolyIsomorphism source middle)
    (second : SourceFPrimeStripFullPolyIsomorphism middle target)
    (third : SourceFPrimeStripFullPolyIsomorphism target final) :
    comp (comp first second) third =
      comp first (comp second third) := by
  refine Quotient.inductionOn₃ first second third ?_
  intro firstRepresentative secondRepresentative thirdRepresentative
  apply Quotient.sound
  exact SourceFPrimeStripHom.NaturallyIsomorphic.assoc
    firstRepresentative secondRepresentative thirdRepresentative

/-- Cancel a selected inverse pair inside a longer composite. -/
theorem comp_inverse_assoc
    (forward : SourceFPrimeStripFullPolyIsomorphism source middle)
    (back : SourceFPrimeStripFullPolyIsomorphism middle source)
    (inverse : comp forward back = id source)
    (next : SourceFPrimeStripFullPolyIsomorphism source target) :
    comp forward (comp back next) = next := by
  rw [← comp_assoc, inverse, id_comp]

end SourceFPrimeStripFullPolyIsomorphism

/--
Remark 5.2.1(i): the D-prime-strip associated to an F-prime-strip.

At a finite place this is the actual base category of the packaged
Frobenioid.  At an infinite place it is the Aut-holomorphic orbispace in the
Kummer collection.  Label classes are the fixed nonzero `l`-torsion labels
modulo sign supplied by the initial theta data.
-/
def SourceFPrimeStrip.associatedD
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
    (strip : SourceFPrimeStrip models) :
    SourceDPrimeStrip models where
  history := strip.history
  nonarchimedean v :=
    (strip.nonarchimedean v).baseCategory
  nonarchimedeanEquivalence v :=
    strip.nonarchimedeanBaseEquivalence v
  archimedean v :=
    (strip.archimedean v).d
  archimedeanIso v :=
    strip.archimedeanOrbispaceIso v
  labelClasses _ :=
    ULift.{u}
      (EtaleTheta.SignLabel
        (EtaleTheta.LTorsionLabel theta.l.value))
  labelEquiv _ := Equiv.ulift
  canonicalLabelClass _ :=
    ULift.up
      (EtaleTheta.canonicalTateSignLabel theta.l.value
        (lt_of_lt_of_le (by decide : 1 < 5) theta.l.ge_five))
  canonicalLabelClass_eq _ := rfl

/-- The componentwise map induced on associated D-prime-strips. -/
def SourceFPrimeStripHom.associatedD
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
    {source target : SourceFPrimeStrip models}
    (f : SourceFPrimeStripHom source target) :
    SourceDPrimeStripHom source.associatedD target.associatedD where
  nonarchimedean v := by
    change
      (source.nonarchimedean v).baseCategory ⥤
        (target.nonarchimedean v).baseCategory
    exact f.nonarchimedeanBase v
  archimedean v := by
    change
      (source.archimedean v).d ⟶
        (target.archimedean v).d
    exact (f.archimedean v).orbispace

/-- The functorial algorithm of Remark 5.2.1(i), on the formal source boundary. -/
def sourceFPrimeStripToD
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta} :
    CategoryTheory.Cat.of (SourceFPrimeStrip models) ⥤
      CategoryTheory.Cat.of (SourceDPrimeStrip models) where
  obj strip := strip.associatedD
  map f := f.associatedD
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Capsules of holomorphic F-prime-strips from Definition 5.2(iii). -/
abbrev SourceFPrimeStripCapsule
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    (models : IUTIThetaHodgeTheaterModels theta) :=
  CategoryCapsule
    (CategoryTheory.Cat.of (SourceFPrimeStrip models))

/--
An isomorphism between objects of `TM^tilde`, retaining both distinguished
factors and the multiplication decomposition.
-/
structure SplitTopologicalMonoidIso
    (source target : SplitTopologicalMonoidPresentation.{u}) where
  total :
    TopologicalMonoidIso source.total target.total
  compactFactor :
    TopologicalMonoidIso
      source.compactFactor target.compactFactor
  noncompactFactor :
    TopologicalMonoidIso
      source.noncompactFactor target.noncompactFactor
  compactInclusion_compatible :
    ∀ value,
      total.toHom (source.compactInclusion value) =
        target.compactInclusion
          (compactFactor.toHom value)
  noncompactInclusion_compatible :
    ∀ value,
      total.toHom (source.noncompactInclusion value) =
        target.noncompactInclusion
          (noncompactFactor.toHom value)
  factorization_compatible :
    ∀ compact noncompact,
      total.toHom
          (source.factorization.toHom
            (compact, noncompact)) =
        target.factorization.toHom
          (compactFactor.toHom compact,
            noncompactFactor.toHom noncompact)

namespace SplitTopologicalMonoidIso

variable
    {source middle target :
      SplitTopologicalMonoidPresentation.{u}}

/-- Identity isomorphism in `TM^tilde`. -/
def refl (source : SplitTopologicalMonoidPresentation.{u}) :
    SplitTopologicalMonoidIso source source where
  total := TopologicalMonoidIso.refl source.total
  compactFactor :=
    TopologicalMonoidIso.refl source.compactFactor
  noncompactFactor :=
    TopologicalMonoidIso.refl source.noncompactFactor
  compactInclusion_compatible _ := rfl
  noncompactInclusion_compatible _ := rfl
  factorization_compatible _ _ := rfl

/-- Composition of isomorphisms in `TM^tilde`. -/
def trans
    (first : SplitTopologicalMonoidIso source middle)
    (second : SplitTopologicalMonoidIso middle target) :
    SplitTopologicalMonoidIso source target where
  total := first.total.trans second.total
  compactFactor :=
    first.compactFactor.trans second.compactFactor
  noncompactFactor :=
    first.noncompactFactor.trans second.noncompactFactor
  compactInclusion_compatible value := by
    change
      second.total.toHom
          (first.total.toHom
            (source.compactInclusion value)) =
        target.compactInclusion
          (second.compactFactor.toHom
            (first.compactFactor.toHom value))
    rw [first.compactInclusion_compatible]
    rw [second.compactInclusion_compatible]
  noncompactInclusion_compatible value := by
    change
      second.total.toHom
          (first.total.toHom
            (source.noncompactInclusion value)) =
        target.noncompactInclusion
          (second.noncompactFactor.toHom
            (first.noncompactFactor.toHom value))
    rw [first.noncompactInclusion_compatible]
    rw [second.noncompactInclusion_compatible]
  factorization_compatible compact noncompact := by
    change
      second.total.toHom
          (first.total.toHom
            (source.factorization.toHom
              (compact, noncompact))) =
        target.factorization.toHom
          (second.compactFactor.toHom
              (first.compactFactor.toHom compact),
            second.noncompactFactor.toHom
              (first.noncompactFactor.toHom noncompact))
    rw [first.factorization_compatible]
    rw [second.factorization_compatible]

end SplitTopologicalMonoidIso

/--
An isomorphism of the archimedean triples in IUT I,
Definition 5.2(ii)(b).
-/
structure ArchimedeanSplitFrobenioidEquivalence
    (source target : ArchimedeanSplitFrobenioidPresentation.{u}) where
  frobenioid :
    SplitFrobenioidEquivalence
      source.frobenioid target.frobenioid
  selectedSplitting_compatible :
    frobenioid.splittingIndexEquiv source.selectedSplitting =
      target.selectedSplitting
  topologicalSplitting :
    SplitTopologicalMonoidIso
      source.topologicalSplitting
      target.topologicalSplitting
  referenceIso :
    frobenioid.carrier.functor.obj source.referenceObject ≅
      target.referenceObject
  referenceTransport :
    target.frobenioid.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
        (frobenioid.carrier.functor.obj source.referenceObject) ≃*
      target.frobenioid.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
        target.referenceObject
  referenceTransport_hom :
    ∀ value,
      (referenceTransport value).hom =
        referenceIso.inv ≫
          value.hom ≫ referenceIso.hom
  rationalTotal_compatible :
    ∀ value :
      source.frobenioid.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
        source.referenceObject,
      target.rationalTotalIso
          (referenceTransport
            (frobenioid.rationalMonoidIso
              { obj := source.referenceObject
                isotropic := source.referenceObject_isotropic }
              value)) =
        topologicalSplitting.total.toHom
          (source.rationalTotalIso value)

namespace ArchimedeanSplitFrobenioidEquivalence

variable
    {source middle target :
      ArchimedeanSplitFrobenioidPresentation.{u}}

/-- Identity equivalence of an archimedean split-Frobenioid triple. -/
def refl (source : ArchimedeanSplitFrobenioidPresentation.{u}) :
    ArchimedeanSplitFrobenioidEquivalence source source where
  frobenioid :=
    SplitFrobenioidEquivalence.refl source.frobenioid
  selectedSplitting_compatible := rfl
  topologicalSplitting :=
    SplitTopologicalMonoidIso.refl
      source.topologicalSplitting
  referenceIso := Iso.refl source.referenceObject
  referenceTransport := MulEquiv.refl _
  referenceTransport_hom value := by
    change
      value.hom =
        𝟙 source.referenceObject ≫
          value.hom ≫ 𝟙 source.referenceObject
    rw [Category.id_comp]
    exact (Category.comp_id value.hom).symm
  rationalTotal_compatible _ := rfl

/-- Composition of archimedean split-Frobenioid equivalences. -/
def trans
    (first :
      ArchimedeanSplitFrobenioidEquivalence source middle)
    (second :
      ArchimedeanSplitFrobenioidEquivalence middle target) :
    ArchimedeanSplitFrobenioidEquivalence source target where
  frobenioid :=
    first.frobenioid.trans second.frobenioid
  selectedSplitting_compatible := by
    change
      second.frobenioid.splittingIndexEquiv
          (first.frobenioid.splittingIndexEquiv
            source.selectedSplitting) =
        target.selectedSplitting
    rw [first.selectedSplitting_compatible]
    exact second.selectedSplitting_compatible
  topologicalSplitting :=
    first.topologicalSplitting.trans
      second.topologicalSplitting
  referenceIso :=
    second.frobenioid.carrier.functor.mapIso
        first.referenceIso ≪≫
      second.referenceIso
  referenceTransport :=
    (second.frobenioid.rationalMonoidIso
        { obj :=
            first.frobenioid.carrier.functor.obj
              source.referenceObject
          isotropic :=
            first.frobenioid.map_isotropic
              { obj := source.referenceObject
                isotropic :=
                  source.referenceObject_isotropic } }).symm |>.trans
      (first.referenceTransport.trans
        ((second.frobenioid.rationalMonoidIso
            { obj := middle.referenceObject
              isotropic :=
                middle.referenceObject_isotropic }).trans
          second.referenceTransport))
  referenceTransport_hom value := by
    let sourceReference :
        source.frobenioid.frobenioid.preFrobenioid.IsotropicLinearObject :=
      { obj := source.referenceObject
        isotropic := source.referenceObject_isotropic }
    let firstMappedReference :
        middle.frobenioid.frobenioid.preFrobenioid.IsotropicLinearObject :=
      { obj :=
          first.frobenioid.carrier.functor.obj
            source.referenceObject
        isotropic :=
          first.frobenioid.map_isotropic sourceReference }
    let preimage :=
      (second.frobenioid.rationalMonoidIso
        firstMappedReference).symm value
    have hpreimage :
        second.frobenioid.carrier.functor.map preimage.hom =
          value.hom := by
      have h :=
        second.frobenioid.rationalMonoidIso_hom
          firstMappedReference preimage
      have happly :
          second.frobenioid.rationalMonoidIso
              firstMappedReference preimage =
            value :=
        (second.frobenioid.rationalMonoidIso
          firstMappedReference).apply_symm_apply value
      rw [happly] at h
      exact h.symm
    change
      (second.referenceTransport
        (second.frobenioid.rationalMonoidIso
          { obj := middle.referenceObject
            isotropic :=
              middle.referenceObject_isotropic }
          (first.referenceTransport preimage))).hom =
        (second.frobenioid.carrier.functor.mapIso
              first.referenceIso ≪≫
            second.referenceIso).inv ≫
          value.hom ≫
        (second.frobenioid.carrier.functor.mapIso
              first.referenceIso ≪≫
            second.referenceIso).hom
    rw [second.referenceTransport_hom]
    rw [second.frobenioid.rationalMonoidIso_hom]
    rw [first.referenceTransport_hom]
    simp only [Functor.map_comp, Iso.trans_hom,
      Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Category.assoc]
    rw [hpreimage]
    rfl
  rationalTotal_compatible value := by
    let sourceReference :
        source.frobenioid.frobenioid.preFrobenioid.IsotropicLinearObject :=
      { obj := source.referenceObject
        isotropic := source.referenceObject_isotropic }
    let firstMappedReference :
        middle.frobenioid.frobenioid.preFrobenioid.IsotropicLinearObject :=
      { obj :=
          first.frobenioid.carrier.functor.obj
            source.referenceObject
        isotropic :=
          first.frobenioid.map_isotropic sourceReference }
    change
      target.rationalTotalIso
          (second.referenceTransport
            (second.frobenioid.rationalMonoidIso
              { obj := middle.referenceObject
                isotropic :=
                  middle.referenceObject_isotropic }
              (first.referenceTransport
                ((second.frobenioid.rationalMonoidIso
                    firstMappedReference).symm
                  (second.frobenioid.rationalMonoidIso
                    firstMappedReference
                    (first.frobenioid.rationalMonoidIso
                      sourceReference value)))))) =
        second.topologicalSplitting.total.toHom
          (first.topologicalSplitting.total.toHom
            (source.rationalTotalIso value))
    rw [MulEquiv.symm_apply_apply]
    rw [second.rationalTotal_compatible]
    rw [first.rationalTotal_compatible]

end ArchimedeanSplitFrobenioidEquivalence

/-! ## Section 0 relations for mono-analytic model comparisons -/

/--
The Section 0 relation on split-Frobenioid equivalences: carrier equivalences
are compared by natural isomorphism and the induced permutation of the
splitting collection is retained pointwise.
-/
structure SplitFrobenioidEquivalence.NaturallyIsomorphic
    {source target : SplitFrobenioidPresentation.{u}}
    (first second : SplitFrobenioidEquivalence source target) : Prop where
  carrier : Nonempty (first.carrier.functor ≅ second.carrier.functor)
  splittingIndex :
    ∀ index,
      first.splittingIndexEquiv index =
        second.splittingIndexEquiv index

namespace SplitFrobenioidEquivalence.NaturallyIsomorphic

variable
    {source middle target final : SplitFrobenioidPresentation.{u}}

protected def refl
    (map : SplitFrobenioidEquivalence source target) :
    map.NaturallyIsomorphic map where
  carrier := ⟨Iso.refl _⟩
  splittingIndex _ := rfl

protected def symm
    {first second : SplitFrobenioidEquivalence source target}
    (relation : first.NaturallyIsomorphic second) :
    second.NaturallyIsomorphic first where
  carrier := relation.carrier.map Iso.symm
  splittingIndex index := (relation.splittingIndex index).symm

protected def trans
    {first second third : SplitFrobenioidEquivalence source target}
    (firstSecond : first.NaturallyIsomorphic second)
    (secondThird : second.NaturallyIsomorphic third) :
    first.NaturallyIsomorphic third where
  carrier := by
    rcases firstSecond.carrier with ⟨firstIso⟩
    rcases secondThird.carrier with ⟨secondIso⟩
    exact ⟨firstIso.trans secondIso⟩
  splittingIndex index :=
    (firstSecond.splittingIndex index).trans
      (secondThird.splittingIndex index)

/-- Horizontal composition of split-Frobenioid natural-isomorphism classes. -/
protected def comp
    {first first' : SplitFrobenioidEquivalence source middle}
    {second second' : SplitFrobenioidEquivalence middle target}
    (hFirst : first.NaturallyIsomorphic first')
    (hSecond : second.NaturallyIsomorphic second') :
    (first.trans second).NaturallyIsomorphic
      (first'.trans second') where
  carrier := by
    rcases hFirst.carrier with ⟨firstIso⟩
    rcases hSecond.carrier with ⟨secondIso⟩
    exact ⟨NatIso.hcomp firstIso secondIso⟩
  splittingIndex index := by
    change
      second.splittingIndexEquiv
          (first.splittingIndexEquiv index) =
        second'.splittingIndexEquiv
          (first'.splittingIndexEquiv index)
    rw [hFirst.splittingIndex, hSecond.splittingIndex]

/-- Associativity is the associator natural isomorphism on carriers. -/
protected def assoc
    (first : SplitFrobenioidEquivalence source middle)
    (second : SplitFrobenioidEquivalence middle target)
    (third : SplitFrobenioidEquivalence target final) :
    ((first.trans second).trans third).NaturallyIsomorphic
      (first.trans (second.trans third)) where
  carrier :=
    ⟨eqToIso (Functor.assoc first.carrier.functor
      second.carrier.functor third.carrier.functor)⟩
  splittingIndex _ := rfl

end SplitFrobenioidEquivalence.NaturallyIsomorphic

/--
Natural isomorphism of archimedean split-Frobenioid maps.  The categorical
part uses the Section 0 relation; the three maps of the split topological
monoid remain actual pointwise maps.
-/
structure ArchimedeanSplitFrobenioidEquivalence.NaturallyIsomorphic
    {source target : ArchimedeanSplitFrobenioidPresentation.{u}}
    (first second :
      ArchimedeanSplitFrobenioidEquivalence source target) : Prop where
  frobenioid :
    first.frobenioid.NaturallyIsomorphic second.frobenioid
  total :
    ∀ value,
      first.topologicalSplitting.total.toHom value =
        second.topologicalSplitting.total.toHom value
  compactFactor :
    ∀ value,
      first.topologicalSplitting.compactFactor.toHom value =
        second.topologicalSplitting.compactFactor.toHom value
  noncompactFactor :
    ∀ value,
      first.topologicalSplitting.noncompactFactor.toHom value =
        second.topologicalSplitting.noncompactFactor.toHom value

namespace ArchimedeanSplitFrobenioidEquivalence.NaturallyIsomorphic

variable
    {source middle target final :
      ArchimedeanSplitFrobenioidPresentation.{u}}

protected def refl
    (map : ArchimedeanSplitFrobenioidEquivalence source target) :
    map.NaturallyIsomorphic map where
  frobenioid := .refl _
  total _ := rfl
  compactFactor _ := rfl
  noncompactFactor _ := rfl

protected def symm
    {first second :
      ArchimedeanSplitFrobenioidEquivalence source target}
    (relation : first.NaturallyIsomorphic second) :
    second.NaturallyIsomorphic first where
  frobenioid := relation.frobenioid.symm
  total value := (relation.total value).symm
  compactFactor value := (relation.compactFactor value).symm
  noncompactFactor value := (relation.noncompactFactor value).symm

protected def trans
    {first second third :
      ArchimedeanSplitFrobenioidEquivalence source target}
    (firstSecond : first.NaturallyIsomorphic second)
    (secondThird : second.NaturallyIsomorphic third) :
    first.NaturallyIsomorphic third where
  frobenioid := firstSecond.frobenioid.trans secondThird.frobenioid
  total value :=
    (firstSecond.total value).trans (secondThird.total value)
  compactFactor value :=
    (firstSecond.compactFactor value).trans
      (secondThird.compactFactor value)
  noncompactFactor value :=
    (firstSecond.noncompactFactor value).trans
      (secondThird.noncompactFactor value)

/-- Composition preserves the archimedean structured relation. -/
protected def comp
    {first first' :
      ArchimedeanSplitFrobenioidEquivalence source middle}
    {second second' :
      ArchimedeanSplitFrobenioidEquivalence middle target}
    (hFirst : first.NaturallyIsomorphic first')
    (hSecond : second.NaturallyIsomorphic second') :
    (first.trans second).NaturallyIsomorphic
      (first'.trans second') where
  frobenioid := hFirst.frobenioid.comp hSecond.frobenioid
  total value := by
    change
      second.topologicalSplitting.total.toHom
          (first.topologicalSplitting.total.toHom value) =
        second'.topologicalSplitting.total.toHom
          (first'.topologicalSplitting.total.toHom value)
    rw [hFirst.total, hSecond.total]
  compactFactor value := by
    change
      second.topologicalSplitting.compactFactor.toHom
          (first.topologicalSplitting.compactFactor.toHom value) =
        second'.topologicalSplitting.compactFactor.toHom
          (first'.topologicalSplitting.compactFactor.toHom value)
    rw [hFirst.compactFactor, hSecond.compactFactor]
  noncompactFactor value := by
    change
      second.topologicalSplitting.noncompactFactor.toHom
          (first.topologicalSplitting.noncompactFactor.toHom value) =
        second'.topologicalSplitting.noncompactFactor.toHom
          (first'.topologicalSplitting.noncompactFactor.toHom value)
    rw [hFirst.noncompactFactor, hSecond.noncompactFactor]

/-- Associativity of archimedean structured maps in the coarsification. -/
protected def assoc
    (first : ArchimedeanSplitFrobenioidEquivalence source middle)
    (second : ArchimedeanSplitFrobenioidEquivalence middle target)
    (third : ArchimedeanSplitFrobenioidEquivalence target final) :
    ((first.trans second).trans third).NaturallyIsomorphic
      (first.trans (second.trans third)) where
  frobenioid := .assoc _ _ _
  total _ := rfl
  compactFactor _ := rfl
  noncompactFactor _ := rfl

end ArchimedeanSplitFrobenioidEquivalence.NaturallyIsomorphic

/--
A mono-analytic Frobenioid-prime-strip from IUT I,
Definition 5.2(ii).

Finite components are actual split Frobenioids.  Infinite components are the
paper's Frobenioid/`TM^tilde`/splitting triples.  Each component is equipped
with the corresponding structure-preserving equivalence to Examples 3.2-3.4.
-/
structure SourceFMonoAnalyticPrimeStrip
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
  nonarchimedean :
    SourceSelectedFinitePlace theta ->
      SplitFrobenioidPresentation.{u}
  nonarchimedeanEquivalence :
    ∀ v,
      SplitFrobenioidEquivalence
        (nonarchimedean v)
        (models.nonarchimedean v).fTildeSplit
  nonarchimedeanEquivalenceFromModel :
    ∀ v,
      SplitFrobenioidEquivalence
        (models.nonarchimedean v).fTildeSplit
        (nonarchimedean v)
  nonarchimedeanToFrom :
    ∀ v,
      ((nonarchimedeanEquivalence v).trans
        (nonarchimedeanEquivalenceFromModel v)).NaturallyIsomorphic
          (SplitFrobenioidEquivalence.refl (nonarchimedean v))
  nonarchimedeanFromTo :
    ∀ v,
      ((nonarchimedeanEquivalenceFromModel v).trans
        (nonarchimedeanEquivalence v)).NaturallyIsomorphic
          (SplitFrobenioidEquivalence.refl
            (models.nonarchimedean v).fTildeSplit)
  archimedean :
    SourceSelectedInfinitePlace theta ->
      ArchimedeanSplitFrobenioidPresentation.{u}
  archimedeanEquivalence :
    ∀ v,
      ArchimedeanSplitFrobenioidEquivalence
        (archimedean v)
        (models.archimedean v).fTildeMonoAnalytic
  archimedeanEquivalenceFromModel :
    ∀ v,
      ArchimedeanSplitFrobenioidEquivalence
        (models.archimedean v).fTildeMonoAnalytic
        (archimedean v)
  archimedeanToFrom :
    ∀ v,
      ((archimedeanEquivalence v).trans
        (archimedeanEquivalenceFromModel v)).NaturallyIsomorphic
          (ArchimedeanSplitFrobenioidEquivalence.refl (archimedean v))
  archimedeanFromTo :
    ∀ v,
      ((archimedeanEquivalenceFromModel v).trans
        (archimedeanEquivalence v)).NaturallyIsomorphic
          (ArchimedeanSplitFrobenioidEquivalence.refl
            (models.archimedean v).fTildeMonoAnalytic)

/--
A globally realified mono-analytic F-prime-strip from IUT I,
Definition 5.2(iv).

The global Frobenioid, prime/place bijection, local mono-analytic strip, and
all currency-exchange maps are present.  The final fields express the
required isomorphism with the canonical Example 3.5 collection
componentwise.
-/
structure SourceFGloballyRealifiedMonoAnalyticPrimeStrip
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
  globalFrobenioid : FrobenioidPresentation.{u}
  globalEquivalence :
    CategoryTheory.Equivalence
      globalFrobenioid.carrier
      models.global.frobenioid.carrier
  Prime : Type u
  primeEquivSelectedPlace :
    Prime ≃
      {v : ThetaPlace K //
        v ∈ theta.valuations.selectedPlaces}
  primeModelEquiv : Prime ≃ models.global.Prime
  prime_compatible :
    ∀ prime,
      models.global.primeEquivSelectedPlace
          (primeModelEquiv prime) =
        primeEquivSelectedPlace prime
  monoAnalytic :
    SourceFMonoAnalyticPrimeStrip models
  characteristicLocal :
    (v : {v : ThetaPlace K //
      v ∈ theta.valuations.selectedPlaces}) ->
      TopologicalMonoidPresentation.{u}
  realifiedLocal :
    (v : {v : ThetaPlace K //
      v ∈ theta.valuations.selectedPlaces}) ->
      TopologicalMonoidPresentation.{u}
  rho :
    ∀ v,
      TopologicalMonoidIso
        (characteristicLocal v) (realifiedLocal v)
  characteristicLocalIso :
    ∀ v,
      TopologicalMonoidIso
        (characteristicLocal v)
        (models.global.characteristicLocal v)
  realifiedLocalIso :
    ∀ v,
      TopologicalMonoidIso
        (realifiedLocal v)
        (models.global.realifiedLocal v)
  rho_compatible :
    ∀ v value,
      (models.global.rho v).toHom
          ((characteristicLocalIso v).toHom value) =
        (realifiedLocalIso v).toHom
          ((rho v).toHom value)

/--
A theta-Hodge theater in the sense of IUT I, Definition 3.6, relative to a
fixed collection of source models.

The finite-place and global categories are required to carry packaged
Frobenioid structures; equivalences are actual categorical equivalences.
Transport of every reconstructed structure across those equivalences remains
the Corollary 4.11(iv) obligation.
-/
structure SourceThetaHodgeTheater
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
  history : SourceThetaArithmeticHistory theta
  nonarchimedean :
    ∀ v : SourceSelectedFinitePlace theta,
      IUTINonarchimedeanLocalModel theta v
  nonarchimedeanEquivalence :
    ∀ v,
      CategoryTheory.Equivalence
        (nonarchimedean v).frobenioid.carrier
        (models.nonarchimedean v).frobenioid.carrier
  nonarchimedeanDTildeEquivalence :
    ∀ v,
      CategoryTheory.Equivalence
        (nonarchimedean v).dTilde
        (models.nonarchimedean v).dTilde
  nonarchimedeanDThetaEquivalence :
    ∀ v,
      CategoryTheory.Equivalence
        (nonarchimedean v).dTheta
        (models.nonarchimedean v).dTheta
  nonarchimedeanFTildeEquivalence :
    ∀ v,
      CategoryTheory.Equivalence
        (nonarchimedean v).fTilde
        (models.nonarchimedean v).fTilde
  nonarchimedeanFThetaEquivalence :
    ∀ v,
      CategoryTheory.Equivalence
        (nonarchimedean v).fTheta
        (models.nonarchimedean v).fTheta
  nonarchimedeanUnitsTildeIso :
    ∀ v,
      TopologicalMonoidIso
        (nonarchimedean v).unitsTilde
        (models.nonarchimedean v).unitsTilde
  nonarchimedeanUnitsThetaIso :
    ∀ v,
      TopologicalMonoidIso
        (nonarchimedean v).unitsTheta
        (models.nonarchimedean v).unitsTheta
  nonarchimedeanUnitsTautological_compatible :
    ∀ v x,
      (nonarchimedeanUnitsThetaIso v).toHom
          ((nonarchimedean v).unitsTautological.toHom x) =
        (models.nonarchimedean v).unitsTautological.toHom
          ((nonarchimedeanUnitsTildeIso v).toHom x)
  archimedean :
    ∀ v : SourceSelectedInfinitePlace theta,
      IUTIArchimedeanLocalModel theta v
  archimedeanCategoryEquivalence :
    ∀ v,
      CategoryTheory.Equivalence
        (archimedean v).c
        (models.archimedean v).c
  archimedeanOrbispaceIso :
    ∀ v,
      AutHolomorphicOrbispaceIso
        (archimedean v).d (models.archimedean v).d
  archimedeanUnitIso :
    ∀ v,
      TopologicalMonoidIso
        (archimedean v).units
        (models.archimedean v).units
  archimedeanKummer_compatible :
    ∀ v x,
      (models.archimedean v).kummer
          ((archimedeanUnitIso v).toHom x) =
        (archimedeanOrbispaceIso v).automorphisms.toHom
          ((archimedean v).kummer x)
  archimedeanDTildeIso :
    ∀ v,
      AutHolomorphicOrbispaceIso
        (archimedean v).dTilde (models.archimedean v).dTilde
  archimedeanDThetaIso :
    ∀ v,
      AutHolomorphicOrbispaceIso
        (archimedean v).dTheta (models.archimedean v).dTheta
  archimedeanFTildeEquivalence :
    ∀ v,
      CategoryTheory.Equivalence
        (archimedean v).fTilde (models.archimedean v).fTilde
  archimedeanFThetaEquivalence :
    ∀ v,
      CategoryTheory.Equivalence
        (archimedean v).fTheta (models.archimedean v).fTheta
  archimedeanUnitsTildeIso :
    ∀ v,
      TopologicalMonoidIso
        (archimedean v).unitsTilde
        (models.archimedean v).unitsTilde
  archimedeanUnitsThetaIso :
    ∀ v,
      TopologicalMonoidIso
        (archimedean v).unitsTheta
        (models.archimedean v).unitsTheta
  archimedeanUnitsTautological_compatible :
    ∀ v x,
      (archimedeanUnitsThetaIso v).toHom
          ((archimedean v).unitsTautological.toHom x) =
        (models.archimedean v).unitsTautological.toHom
          ((archimedeanUnitsTildeIso v).toHom x)
  global : IUTIGlobalFrobenioidModel theta
  globalCategoryEquivalence :
    CategoryTheory.Equivalence
      global.frobenioid.carrier models.global.frobenioid.carrier
  thetaGlobalCategoryEquivalence :
    CategoryTheory.Equivalence
      global.thetaGlobal.carrier models.global.thetaGlobal.carrier
  dGlobalCategoryEquivalence :
    CategoryTheory.Equivalence
      global.dGlobal.carrier models.global.dGlobal.carrier
  globalPrimeEquivalence :
    global.Prime ≃ models.global.Prime
  primeCompatibility :
    ∀ p,
      models.global.primeEquivSelectedPlace
          (globalPrimeEquivalence p) =
        global.primeEquivSelectedPlace p

namespace SourceThetaHodgeTheater

/--
The structure-preserving transport needed before the mono-analytic
`F^\vdash`-prime-strip of a theta-Hodge theater may be formed.

The bare equivalences between the `F^tilde` carrier categories stored by the
theater do not determine the rational-monoid transport, the characteristic
splittings, or the selected archimedean splitting.  Both directions of the
structure-preserving comparison are retained so that full theta-link members
can be composed through the common model.  IUT II, Corollaries 4.5 and 4.6,
construct precisely this stronger data.
-/
structure MonoAnalyticTransport
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
    (theater : SourceThetaHodgeTheater models) where
  nonarchimedean :
    ∀ v,
      SplitFrobenioidEquivalence
        (theater.nonarchimedean v).fTildeSplit
        (models.nonarchimedean v).fTildeSplit
  nonarchimedeanFromModel :
    ∀ v,
      SplitFrobenioidEquivalence
        (models.nonarchimedean v).fTildeSplit
        (theater.nonarchimedean v).fTildeSplit
  nonarchimedeanToFrom :
    ∀ v,
      ((nonarchimedean v).trans
        (nonarchimedeanFromModel v)).NaturallyIsomorphic
          (SplitFrobenioidEquivalence.refl
            (theater.nonarchimedean v).fTildeSplit)
  nonarchimedeanFromTo :
    ∀ v,
      ((nonarchimedeanFromModel v).trans
        (nonarchimedean v)).NaturallyIsomorphic
          (SplitFrobenioidEquivalence.refl
            (models.nonarchimedean v).fTildeSplit)
  nonarchimedean_carrier_compatible :
    ∀ v,
      (nonarchimedean v).carrier.functor ⋙
          (models.nonarchimedean v).fTildeSplitCarrier.functor =
        (theater.nonarchimedean v).fTildeSplitCarrier.functor ⋙
          (theater.nonarchimedeanFTildeEquivalence v).functor
  archimedean :
    ∀ v,
      ArchimedeanSplitFrobenioidEquivalence
        (theater.archimedean v).fTildeMonoAnalytic
        (models.archimedean v).fTildeMonoAnalytic
  archimedeanFromModel :
    ∀ v,
      ArchimedeanSplitFrobenioidEquivalence
        (models.archimedean v).fTildeMonoAnalytic
        (theater.archimedean v).fTildeMonoAnalytic
  archimedeanToFrom :
    ∀ v,
      ((archimedean v).trans
        (archimedeanFromModel v)).NaturallyIsomorphic
          (ArchimedeanSplitFrobenioidEquivalence.refl
            (theater.archimedean v).fTildeMonoAnalytic)
  archimedeanFromTo :
    ∀ v,
      ((archimedeanFromModel v).trans
        (archimedean v)).NaturallyIsomorphic
          (ArchimedeanSplitFrobenioidEquivalence.refl
            (models.archimedean v).fTildeMonoAnalytic)
  archimedean_carrier_compatible :
    ∀ v,
      (archimedean v).frobenioid.carrier.functor ⋙
          (models.archimedean v).fTildeSplitCarrier.functor =
        (theater.archimedean v).fTildeSplitCarrier.functor ⋙
          (theater.archimedeanFTildeEquivalence v).functor

/--
Construct the actual mono-analytic `F^\vdash`-prime-strip after the required
Corollaries 4.5/4.6 transport has been supplied.
-/
def associatedFMonoAnalytic
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
    (theater : SourceThetaHodgeTheater models)
    (transport : theater.MonoAnalyticTransport) :
    SourceFMonoAnalyticPrimeStrip models where
  nonarchimedean v :=
    (theater.nonarchimedean v).fTildeSplit
  nonarchimedeanEquivalence v :=
    transport.nonarchimedean v
  nonarchimedeanEquivalenceFromModel v :=
    transport.nonarchimedeanFromModel v
  nonarchimedeanToFrom v := transport.nonarchimedeanToFrom v
  nonarchimedeanFromTo v := transport.nonarchimedeanFromTo v
  archimedean v :=
    (theater.archimedean v).fTildeMonoAnalytic
  archimedeanEquivalence v :=
    transport.archimedean v
  archimedeanEquivalenceFromModel v :=
    transport.archimedeanFromModel v
  archimedeanToFrom v := transport.archimedeanToFrom v
  archimedeanFromTo v := transport.archimedeanFromTo v

end SourceThetaHodgeTheater

/--
The F-prime-strip tautologically associated to a theta-Hodge theater, as used
in IUT I, Definition 5.5(ii)(c).
-/
def SourceThetaHodgeTheater.associatedF
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
    (theater : SourceThetaHodgeTheater models) :
    SourceFPrimeStrip models where
  history := theater.history
  nonarchimedean v :=
    (theater.nonarchimedean v).frobenioid
  nonarchimedeanEquivalence v :=
    theater.nonarchimedeanEquivalence v
  nonarchimedeanBaseEquivalence v :=
    (theater.nonarchimedean v).baseDerivedFromCategory |>.trans
      ((theater.nonarchimedean v).derivedFromCategory.symm.trans
        ((theater.nonarchimedeanEquivalence v).trans
          (models.nonarchimedean v).derivedFromCategory))
  archimedean v :=
    theater.archimedean v
  archimedeanCategoryEquivalence v :=
    theater.archimedeanCategoryEquivalence v
  archimedeanOrbispaceIso v :=
    theater.archimedeanOrbispaceIso v
  archimedeanUnitIso v :=
    theater.archimedeanUnitIso v
  kummer_compatible v x :=
    theater.archimedeanKummer_compatible v x

/--
The source convention that an isomorphism of categories is an equivalence
modulo natural isomorphism of its functor.
-/
def categoryEquivalenceSetoid
    (C D : CategoryTheory.Cat.{u, u}) :
    Setoid (CategoryTheory.Equivalence C D) where
  r left right := Nonempty (left.functor ≅ right.functor)
  iseqv := by
    constructor
    · intro e
      exact ⟨Iso.refl e.functor⟩
    · intro left right h
      rcases h with ⟨h⟩
      exact ⟨h.symm⟩
    · intro first second third h₁ h₂
      rcases h₁ with ⟨h₁⟩
      rcases h₂ with ⟨h₂⟩
      exact ⟨h₁.trans h₂⟩

/--
The full poly-isomorphism between two categories: the collection of all
equivalences, quotiented by natural isomorphism, as stipulated in IUT I, §0.
-/
abbrev FullPolyIsomorphism
    (C D : CategoryTheory.Cat.{u, u}) :=
  Quotient (categoryEquivalenceSetoid C D)

namespace FullPolyIsomorphism

/-- The member of the full poly-isomorphism represented by an equivalence. -/
def ofEquivalence
    {C D : CategoryTheory.Cat.{u, u}}
    (e : CategoryTheory.Equivalence C D) :
    FullPolyIsomorphism C D :=
  Quotient.mk (categoryEquivalenceSetoid C D) e

end FullPolyIsomorphism

/--
The categorical core of the theta-link in IUT I, Corollary 3.7(i)-(ii).

The global equivalence goes from the theta-realified global Frobenioid of the
source theater to the moduli global Frobenioid of the target theater.  The
local `Dtilde` components are transported through their common source models.
-/
structure SourceThetaLinkCore
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
    (source target : SourceThetaHodgeTheater models) where
  global :
    CategoryTheory.Equivalence
      source.global.thetaGlobal.carrier
      target.global.frobenioid.carrier
  nonarchimedeanDTilde :
    ∀ v,
      CategoryTheory.Equivalence
        (source.nonarchimedean v).dTilde
        (target.nonarchimedean v).dTilde
  nonarchimedeanUnits :
    ∀ v,
      TopologicalMonoidIso
        (source.nonarchimedean v).unitsTilde
        (target.nonarchimedean v).unitsTilde
  archimedeanUnits :
    ∀ v,
      TopologicalMonoidIso
        (source.archimedean v).unitsTilde
        (target.archimedean v).unitsTilde

namespace SourceThetaLinkCore

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod]
variable [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
variable [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : SourceInitialThetaCore Fmod F K}
variable {models : IUTIThetaHodgeTheaterModels theta}

/--
The theta-link core exists between any two theaters over the same source
models.  This is the categorical transport argument of Corollary 3.7.
-/
def ofTheaters
    (source target : SourceThetaHodgeTheater models) :
    SourceThetaLinkCore source target where
  global :=
    source.thetaGlobalCategoryEquivalence |>.trans <|
      models.global.modToTheta.symm.trans
        target.globalCategoryEquivalence.symm
  nonarchimedeanDTilde := fun v =>
    (source.nonarchimedeanDTildeEquivalence v).trans
      (target.nonarchimedeanDTildeEquivalence v).symm
  nonarchimedeanUnits := fun v =>
    (source.nonarchimedean v).unitsTautological.trans <|
      (source.nonarchimedeanUnitsThetaIso v).trans <|
        (models.nonarchimedean v).unitsTautological.symm.trans
          (target.nonarchimedeanUnitsTildeIso v).symm
  archimedeanUnits := fun v =>
    (source.archimedean v).unitsTautological.trans <|
      (source.archimedeanUnitsThetaIso v).trans <|
        (models.archimedean v).unitsTautological.symm.trans
          (target.archimedeanUnitsTildeIso v).symm

/-- The global member of the source's full poly-isomorphism. -/
def globalFullPolyIsomorphism
    {source target : SourceThetaHodgeTheater models}
    (link : SourceThetaLinkCore source target) :
    FullPolyIsomorphism
      source.global.thetaGlobal.carrier
      target.global.frobenioid.carrier :=
  FullPolyIsomorphism.ofEquivalence link.global

/--
The full poly-isomorphism of global Frobenioid categories is nonempty for any
two theaters over the same source models.
-/
theorem globalFullPolyIsomorphism_nonempty
    (source target : SourceThetaHodgeTheater models) :
    Nonempty
      (FullPolyIsomorphism
        source.global.thetaGlobal.carrier
        target.global.frobenioid.carrier) :=
  ⟨(ofTheaters source target).globalFullPolyIsomorphism⟩

end SourceThetaLinkCore

end Iut
