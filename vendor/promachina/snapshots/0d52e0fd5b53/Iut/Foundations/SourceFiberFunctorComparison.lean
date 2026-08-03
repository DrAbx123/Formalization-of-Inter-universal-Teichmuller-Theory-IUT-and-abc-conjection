/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.CategoryTheory.Galois.Decomposition

/-!
# Comparison of fundamental functors of a connected anabelioid

In *The Geometry of Anabelioids*, immediately before Definition 1.1.2
(printed and PDF page 9), Mochizuki recalls that any two fundamental
functors of a connected anabelioid are isomorphic.  The choice is not
canonical; changing it is the source of the inner-conjugacy ambiguity in
Proposition 1.1.4.

This file derives the comparison from Mathlib's pro-representation of a
fiber functor.  Natural transformations from `F` to `G` are compatible
families of points of `G` on the cofiltered category of pointed Galois
objects of `F`.  Those fibers are finite and nonempty, so their inverse
limit is nonempty.  A transformation between fiber functors is then an
isomorphism: transformations exist in both directions, and both composites
are endomorphisms of fiber functors, hence invertible.

No comparison map is accepted as data.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.PreGaloisCategory
open CategoryTheory.PreGaloisCategory.PointedGaloisObject

namespace SourceFiberFunctorComparison

/-! ## Exact pullback functors preserve fiber functors -/

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
variable [GaloisCategory C] [GaloisCategory D]

/-- An exact functor between connected Galois categories cannot send a
connected object to an initial object. -/
theorem obj_not_initial_of_isConnected
    (pullback : C ⥤ D) [PreservesFiniteLimits pullback]
    [PreservesFiniteColimits pullback]
    (sourceFiber : D ⥤ FintypeCat.{u}) [FiberFunctor sourceFiber]
    (X : C) [IsConnected X] :
    IsInitial (pullback.obj X) → False := by
  intro hInitial
  let targetFiber := GaloisCategory.getFiberFunctor C
  let terminalMap : X ⟶ ⊤_ C := terminal.from X
  have sourceNonempty : Nonempty (targetFiber.obj X) :=
    nonempty_fiber_of_isConnected targetFiber X
  have terminalSurjective :
      Function.Surjective (targetFiber.map terminalMap) := by
    intro point
    obtain ⟨sourcePoint⟩ := sourceNonempty
    refine ⟨sourcePoint, ?_⟩
    have fiberTerminal : IsTerminal (targetFiber.obj (⊤_ C)) :=
      terminalIsTerminal.isTerminalObj targetFiber
    let first : FintypeCat.of PUnit ⟶ targetFiber.obj (⊤_ C) :=
      FintypeCat.homMk fun _ => targetFiber.map terminalMap sourcePoint
    let second : FintypeCat.of PUnit ⟶ targetFiber.obj (⊤_ C) :=
      FintypeCat.homMk fun _ => point
    have equality : first = second := fiberTerminal.hom_ext first second
    exact ConcreteCategory.congr_hom equality PUnit.unit
  letI : Epi (targetFiber.map terminalMap) :=
    ConcreteCategory.epi_of_surjective _ terminalSurjective
  letI : Epi terminalMap :=
    targetFiber.epi_of_epi_map (inferInstance : Epi (targetFiber.map terminalMap))
  letI : Epi (pullback.map terminalMap) := inferInstance
  have mappedTerminal : IsTerminal (pullback.obj (⊤_ C)) :=
    terminalIsTerminal.isTerminalObj pullback
  have fiberMappedTerminal :
      IsTerminal (sourceFiber.obj (pullback.obj (⊤_ C))) :=
    mappedTerminal.isTerminalObj sourceFiber
  let point : sourceFiber.obj (pullback.obj (⊤_ C)) :=
    (fiberMappedTerminal.from (FintypeCat.of PUnit)).hom PUnit.unit
  have surjectiveMappedTerminal :
      Function.Surjective (sourceFiber.map (pullback.map terminalMap)) :=
    surjective_on_fiber_of_epi sourceFiber (pullback.map terminalMap)
  obtain ⟨preimage, _⟩ := surjectiveMappedTerminal point
  exact ((initial_iff_fiber_empty sourceFiber (pullback.obj X)).mp
    ⟨hInitial⟩).false preimage

/-- Exact functors between connected Galois categories reflect initial
objects. -/
noncomputable def reflects_initial
    (pullback : C ⥤ D) [PreservesFiniteLimits pullback]
    [PreservesFiniteColimits pullback]
    (sourceFiber : D ⥤ FintypeCat.{u}) [FiberFunctor sourceFiber]
    (X : C) (hInitial : IsInitial (pullback.obj X)) : IsInitial X := by
  let targetFiber := GaloisCategory.getFiberFunctor C
  apply Classical.choice
  rw [initial_iff_fiber_empty targetFiber X]
  constructor
  intro targetPoint
  obtain ⟨A, mapToX, _, hGalois, _⟩ :=
    exists_hom_from_galois_of_fiber targetFiber X targetPoint
  letI : IsGalois A := hGalois
  letI : IsConnected A := IsGalois.toIsConnected
  have sourceEmpty : IsEmpty (sourceFiber.obj (pullback.obj X)) :=
    (initial_iff_fiber_empty sourceFiber (pullback.obj X)).mp ⟨hInitial⟩
  have mappedGaloisEmpty : IsEmpty (sourceFiber.obj (pullback.obj A)) :=
    ⟨fun point => sourceEmpty.false
      (sourceFiber.map (pullback.map mapToX) point)⟩
  have mappedGaloisInitial : IsInitial (pullback.obj A) :=
    Classical.choice <|
      (initial_iff_fiber_empty sourceFiber (pullback.obj A)).mpr
        mappedGaloisEmpty
  exact obj_not_initial_of_isConnected pullback sourceFiber A
    mappedGaloisInitial

/-- An exact functor between connected Galois categories is faithful. -/
@[implicit_reducible] noncomputable def exactFunctorFaithful
    (pullback : C ⥤ D) [PreservesFiniteLimits pullback]
    [PreservesFiniteColimits pullback]
    (sourceFiber : D ⥤ FintypeCat.{u}) [FiberFunctor sourceFiber] :
    pullback.Faithful where
  map_injective {X Y} first second equality := by
    let equalizerInclusion : equalizer first second ⟶ X :=
      equalizer.ι first second
    haveI : IsIso (equalizer.ι (pullback.map first) (pullback.map second)) :=
      equalizer.ι_of_eq equality
    haveI : IsIso (pullback.map equalizerInclusion) := by
      rw [← equalizerComparison_comp_π first second pullback]
      exact IsIso.comp_isIso
    obtain ⟨complement, complementInclusion, ⟨decomposition⟩⟩ :=
      PreGaloisCategory.monoInducesIsoOnDirectSummand equalizerInclusion
    let mappedDecomposition :
        IsColimit
          (BinaryCofan.mk
            (pullback.map equalizerInclusion)
            (pullback.map complementInclusion)) :=
      mapIsColimitOfPreservesOfIsColimit pullback
        equalizerInclusion complementInclusion decomposition
    let mappedColimit :
        ColimitCocone
          (pair (pullback.obj (equalizer first second))
            (pullback.obj complement)) :=
      { cocone := BinaryCofan.mk
          (pullback.map equalizerInclusion)
          (pullback.map complementInclusion)
        isColimit := mappedDecomposition }
    let decompositionIso :
        pullback.obj X ≅
          pullback.obj (equalizer first second) ⨿
            pullback.obj complement :=
      (colimit.isoColimitCocone mappedColimit).symm
    have cardDecomposition :
        Nat.card (sourceFiber.obj (pullback.obj X)) =
          Nat.card
              (sourceFiber.obj
                (pullback.obj (equalizer first second))) +
            Nat.card (sourceFiber.obj (pullback.obj complement)) := by
      rw [card_fiber_eq_of_iso sourceFiber decompositionIso]
      exact card_fiber_coprod_eq_sum sourceFiber _ _
    have cardEqualizer :
        Nat.card
            (sourceFiber.obj
              (pullback.obj (equalizer first second))) =
          Nat.card (sourceFiber.obj (pullback.obj X)) :=
      card_fiber_eq_of_iso sourceFiber
        (asIso (pullback.map equalizerInclusion))
    have cardComplement :
        Nat.card (sourceFiber.obj (pullback.obj complement)) = 0 := by
      omega
    have mappedComplementInitial : IsInitial (pullback.obj complement) :=
      Classical.choice <|
        (initial_iff_fiber_empty sourceFiber (pullback.obj complement)).mpr
          (Finite.card_eq_zero_iff.mp cardComplement)
    have complementInitial : IsInitial complement :=
      reflects_initial pullback sourceFiber complement mappedComplementInitial
    letI : IsInitial complement := complementInitial
    haveI : IsIso equalizerInclusion :=
      (BinaryCofan.isColimit_iff_isIso_inl complementInitial
        (BinaryCofan.mk equalizerInclusion complementInclusion)).mp
        ⟨decomposition⟩
    exact eq_of_epi_equalizer

/-- An exact functor between connected Galois categories reflects
isomorphisms. -/
@[implicit_reducible] noncomputable def exactFunctorReflectsIsomorphisms
    (pullback : C ⥤ D) [PreservesFiniteLimits pullback]
    [PreservesFiniteColimits pullback]
    (sourceFiber : D ⥤ FintypeCat.{u}) [FiberFunctor sourceFiber] :
    pullback.ReflectsIsomorphisms := by
  letI : pullback.Faithful := exactFunctorFaithful pullback sourceFiber
  let targetFiber := GaloisCategory.getFiberFunctor C
  letI : Balanced C :=
    { isIso_of_mono_of_epi := fun morphism _ _ => by
        haveI : Mono (targetFiber.map morphism) := inferInstance
        haveI : Epi (targetFiber.map morphism) := inferInstance
        have mappedBijective : Function.Bijective (targetFiber.map morphism) := by
          constructor
          · exact ConcreteCategory.injective_of_mono_of_preservesPullback
              (targetFiber.map morphism)
          · exact surjective_on_fiber_of_epi targetFiber morphism
        haveI : IsIso (targetFiber.map morphism) :=
          (ConcreteCategory.isIso_iff_bijective
            (targetFiber.map morphism)).mpr mappedBijective
        exact isIso_of_reflects_iso morphism targetFiber }
  infer_instance

/-- Composing a fiber functor with an exact pullback functor gives a fiber
functor.  In particular, reflection of isomorphisms is derived rather than
added to the definition of an anabelioid morphism. -/
@[implicit_reducible] noncomputable def compFiberFunctor
    (pullback : C ⥤ D) [PreservesFiniteLimits pullback]
    [PreservesFiniteColimits pullback]
    (sourceFiber : D ⥤ FintypeCat.{u}) [FiberFunctor sourceFiber] :
    FiberFunctor (pullback ⋙ sourceFiber) := by
  letI : pullback.ReflectsIsomorphisms :=
    exactFunctorReflectsIsomorphisms pullback sourceFiber
  exact
    { preservesTerminalObjects := inferInstance
      preservesPullbacks := inferInstance
      preservesFiniteCoproducts := inferInstance
      preservesEpis := inferInstance
      preservesQuotientsByFiniteGroups group _ _ := by
        choose smallGroup groupStructure groupFinite groupEquiv using
          Finite.exists_type_univ_nonempty_mulEquiv group
        letI : Group smallGroup := groupStructure
        letI : Fintype smallGroup := groupFinite
        let pullbackPreserves :
            PreservesColimitsOfShape (SingleObj group) pullback :=
          preservesColimitsOfShape_of_equiv
            groupEquiv.some.toSingleObjEquiv.symm pullback
        letI : PreservesColimitsOfShape (SingleObj group) pullback :=
          pullbackPreserves
        letI : PreservesColimitsOfShape (SingleObj group) sourceFiber :=
          inferInstance
        exact comp_preservesColimitsOfShape pullback sourceFiber
      reflectsIsos := inferInstance }

/-! ## Comparison of arbitrary fiber functors -/

variable (F G : C ⥤ FintypeCat.{u}) [FiberFunctor F] [FiberFunctor G]

local notation "F′" => F ⋙ FintypeCat.incl
local notation "G′" => G ⋙ FintypeCat.incl

/-- Natural transformations `F ⟶ G` are compatible families of points of
`G` on the pointed Galois objects of `F`.  This is the two-functor version
of Mathlib's `endEquivSectionsFibers`. -/
noncomputable def natTransEquivSections :
    (F ⟶ G) ≃ (incl F ⋙ G′).sections :=
  let i1 : (F ⟶ G) ≃ (F′ ⟶ G′) :=
    (FullyFaithful.whiskeringRight
      (FullyFaithful.ofFullyFaithful FintypeCat.incl) C).homEquiv
  let i2 : (F′ ⟶ G′) ≅
      (colimit ((incl F).op ⋙ coyoneda) ⟶ G′) :=
    (yoneda.obj G′).mapIso
      (colimit.isoColimitCocone ⟨cocone F, isColimit F⟩).op
  let i3 : (colimit ((incl F).op ⋙ coyoneda) ⟶ G′) ≅
      limit ((incl F ⋙ G′) ⋙ uliftFunctor.{u + 1}) :=
    colimitCoyonedaHomIsoLimit' (incl F) G′
  let i4 : limit (incl F ⋙ G′ ⋙ uliftFunctor.{u + 1}) ≃
      ((incl F ⋙ G′) ⋙ uliftFunctor.{u + 1}).sections :=
    Types.limitEquivSections
      (incl F ⋙ (G ⋙ FintypeCat.incl) ⋙ uliftFunctor.{u + 1, u})
  let i5 : ((incl F ⋙ G′) ⋙ uliftFunctor.{u + 1}).sections ≃
      (incl F ⋙ G′).sections :=
    (Types.sectionsEquiv (incl F ⋙ G′)).symm
  i1.trans <| i2.toEquiv.trans <| i3.toEquiv.trans <| i4.trans i5

/-- There exists a natural transformation between any two fiber functors of
the same connected Galois category. -/
theorem natTrans_nonempty : Nonempty (F ⟶ G) := by
  let diagram := incl F ⋙ G ⋙ FintypeCat.incl
  haveI (A : PointedGaloisObject F) : IsGalois A.obj := A.isGalois
  haveI (A : PointedGaloisObject F) : Nonempty (diagram.obj A) := by
    dsimp [diagram]
    exact nonempty_fiber_of_isConnected G A.obj
  haveI (A : PointedGaloisObject F) : Finite (diagram.obj A) := by
    dsimp [diagram]
    infer_instance
  obtain ⟨compatible, hcompatible⟩ :=
    nonempty_sections_of_finite_cofiltered_system diagram
  exact ⟨(natTransEquivSections F G).symm ⟨compatible, hcompatible⟩⟩

/-- Every natural transformation between two fiber functors is invertible.
The proof uses a transformation in the reverse direction and the fact that
all endomorphisms of a fiber functor are isomorphisms. -/
theorem natTrans_isIso (transformation : F ⟶ G) : IsIso transformation := by
  let reverse : G ⟶ F := Classical.choice (natTrans_nonempty G F)
  letI : IsIso (transformation ≫ reverse) :=
    FibreFunctor.end_isIso F (transformation ≫ reverse)
  letI : IsIso (reverse ≫ transformation) :=
    FibreFunctor.end_isIso G (reverse ≫ transformation)
  let rightInverse : G ⟶ F :=
    reverse ≫ inv (transformation ≫ reverse)
  let leftInverse : G ⟶ F :=
    inv (reverse ≫ transformation) ≫ reverse
  have homRightInverse : transformation ≫ rightInverse = 𝟙 F := by
    dsimp [rightInverse]
    rw [← Category.assoc, IsIso.hom_inv_id]
  have leftInverseHom : leftInverse ≫ transformation = 𝟙 G := by
    dsimp [leftInverse]
    rw [Category.assoc, IsIso.inv_hom_id]
  have inverseEquality : rightInverse = leftInverse := by
    calc
      rightInverse = 𝟙 G ≫ rightInverse := by simp
      _ = (leftInverse ≫ transformation) ≫ rightInverse := by
        rw [leftInverseHom]
      _ = leftInverse ≫ (transformation ≫ rightInverse) := by simp
      _ = leftInverse ≫ 𝟙 F := by rw [homRightInverse]
      _ = leftInverse := by simp
  exact
    ⟨⟨rightInverse, homRightInverse, by
      rw [inverseEquality]
      exact leftInverseHom⟩⟩

/-- Any two fundamental functors of a connected anabelioid are isomorphic.
The isomorphism is selected from the preceding existence proof; it is not
part of the input data. -/
noncomputable def fiberFunctorIso : F ≅ G := by
  let transformation : F ⟶ G :=
    Classical.choice (natTrans_nonempty F G)
  letI : IsIso transformation := natTrans_isIso F G transformation
  exact asIso transformation

end SourceFiberFunctorComparison

end Iut
