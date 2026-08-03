/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceAnabelioidComponents

/-!
# Connected finite-action slices

Remark 1.2.2.1 of Mochizuki's *The Geometry of Anabelioids* identifies a
connected finite-etale morphism with restriction along an open subgroup.
For the continuous-action model, the first converse step is to show that a
slice equivalent to a connected anabelioid is cut out by a transitive action.

This file proves that step categorically.  The terminal object of a Galois
category is connected, connectedness is invariant under categorical
equivalence, and an orbit inclusion is a noninitial monomorphism into the
terminal object of the slice.  It must therefore be an isomorphism.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

/-! ## Categorical connectedness under equivalence -/

/-- Connectedness of an object is invariant under isomorphism. -/
theorem sourceIsConnected_of_iso
    {C : Type (u + 1)} [Category.{u} C]
    {X Y : C} (connected : IsConnected X) (iso : X ≅ Y) :
    IsConnected Y where
  notInitial initialY :=
    connected.notInitial (initialY.ofIso iso.symm)
  noTrivialComponent Z inclusion _ := by
    intro noninitial
    let pulledInclusion : Z ⟶ X := inclusion ≫ iso.inv
    haveI : Mono pulledInclusion := inferInstance
    haveI : IsIso pulledInclusion :=
      connected.noTrivialComponent Z pulledInclusion noninitial
    exact IsIso.of_isIso_comp_right inclusion iso.inv

/-- A categorical equivalence carries connected objects to connected
objects. -/
theorem sourceIsConnected_equivalence_functor
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (equivalence : C ≌ D) {X : C} (connected : IsConnected X) :
    IsConnected (equivalence.functor.obj X) where
  notInitial initialImage := by
    have initialInverse :
        IsInitial (equivalence.inverse.obj
          (equivalence.functor.obj X)) :=
      initialImage.isInitialObj equivalence.inverse
    exact connected.notInitial
      (initialInverse.ofIso (equivalence.unitIso.app X).symm)
  noTrivialComponent Y inclusion _ := by
    intro noninitial
    have inverseNoninitial :
        IsInitial (equivalence.inverse.obj Y) → False := by
      intro initialInverse
      have initialRoundTrip :
          IsInitial (equivalence.functor.obj
            (equivalence.inverse.obj Y)) :=
        initialInverse.isInitialObj equivalence.functor
      exact noninitial
        (initialRoundTrip.ofIso (equivalence.counitIso.app Y))
    haveI : Mono (equivalence.inverse.map inclusion) := inferInstance
    have inverseImageConnected :
        IsConnected
          (equivalence.inverse.obj
            (equivalence.functor.obj X)) :=
      sourceIsConnected_of_iso connected (equivalence.unitIso.app X)
    haveI : IsIso (equivalence.inverse.map inclusion) :=
      inverseImageConnected.noTrivialComponent
        (equivalence.inverse.obj Y)
        (equivalence.inverse.map inclusion)
        inverseNoninitial
    exact isIso_of_reflects_iso inclusion equivalence.inverse

/-- The terminal object of a Galois category is connected. -/
theorem sourceGaloisCategory_isConnected_of_isTerminal
    {C : Type (u + 1)} [Category.{u} C] [GaloisCategory C]
    (T : C) (terminal : IsTerminal T) :
    IsConnected T := by
  let fiber := GaloisCategory.getFiberFunctor C
  letI : PreservesFiniteLimits fiber := inferInstance
  letI : fiber.PreservesMonomorphisms := inferInstance
  have fiberTerminal : IsTerminal (fiber.obj T) :=
    terminal.isTerminalObj fiber
  refine
    { notInitial := ?_
      noTrivialComponent := ?_ }
  · intro initial
    have fiberEmpty : IsEmpty (fiber.obj T) :=
      (initial_iff_fiber_empty fiber T).mp ⟨initial⟩
    let point : fiber.obj T :=
      fiberTerminal.from (FintypeCat.of PUnit) PUnit.unit
    exact isEmptyElim point
  · intro Y inclusion _ noninitial
    haveI : Mono (fiber.map inclusion) := inferInstance
    have fiberSourceNonempty : Nonempty (fiber.obj Y) :=
      (not_initial_iff_fiber_nonempty fiber Y).mp noninitial
    have fiberTargetSubsingleton :
        ∀ first second : fiber.obj T, first = second := by
      intro first second
      let firstMap : FintypeCat.of PUnit ⟶ fiber.obj T :=
        FintypeCat.homMk fun _ => first
      let secondMap : FintypeCat.of PUnit ⟶ fiber.obj T :=
        FintypeCat.homMk fun _ => second
      have equality := fiberTerminal.hom_ext firstMap secondMap
      exact ConcreteCategory.congr_hom equality PUnit.unit
    have fiberMapBijective :
        Function.Bijective (fiber.map inclusion) := by
      constructor
      · exact
          (ConcreteCategory.mono_iff_injective_of_preservesPullback
            (fiber.map inclusion)).mp inferInstance
      · intro targetPoint
        obtain ⟨sourcePoint⟩ := fiberSourceNonempty
        exact
          ⟨sourcePoint,
            fiberTargetSubsingleton
              (fiber.map inclusion sourcePoint) targetPoint⟩
    haveI : IsIso (fiber.map inclusion) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr fiberMapBijective
    exact isIso_of_reflects_iso inclusion fiber

/-- Under an equivalence from a Galois category, every terminal target object
is connected. -/
theorem sourceGaloisCategory_equivalence_terminal_isConnected
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [GaloisCategory C] (equivalence : C ≌ D)
    (T : D) (terminal : IsTerminal T) :
    IsConnected T := by
  have inverseTerminal :
      IsTerminal (equivalence.inverse.obj T) :=
    terminal.isTerminalObj equivalence.inverse
  have inverseConnected :
      IsConnected (equivalence.inverse.obj T) :=
    sourceGaloisCategory_isConnected_of_isTerminal
      (equivalence.inverse.obj T) inverseTerminal
  have roundTripConnected :
      IsConnected
        (equivalence.functor.obj (equivalence.inverse.obj T)) :=
    sourceIsConnected_equivalence_functor equivalence inverseConnected
  exact sourceIsConnected_of_iso
    roundTripConnected (equivalence.counitIso.app T)

/-! ## Connected slices have one orbit -/

/-- One orbit, regarded as a subobject of the terminal object of the slice,
is not initial. -/
theorem sourceActionComponentOver_notInitial
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    IsInitial
      (Over.mk (sourceActionComponentInclusion G S component)) → False := by
  intro initialComponent
  have initialAction :
      IsInitial (sourceActionComponentAction G S component) := by
    exact initialComponent.isInitialObj (Over.forget S)
  have emptyFiber :
      IsEmpty
        ((continuousActionFiber G).obj
          (sourceActionComponentAction G S component)) :=
    (initial_iff_fiber_empty
      (continuousActionFiber G)
      (sourceActionComponentAction G S component)).mp
        ⟨initialAction⟩
  let point : SourceActionComponentFiber G S component :=
    ⟨component.out, Quotient.out_eq component⟩
  exact emptyFiber.false point

/-- If a slice is equivalent to a connected anabelioid, every orbit
inclusion into the slicing action is an isomorphism. -/
theorem sourceActionComponentInclusion_isIso_of_equivalentToGalois
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    {C : Type (u + 1)} [Category.{u} C] [GaloisCategory C]
    (equivalence : C ≌ Over S)
    (component : SourceActionComponent G S) :
    IsIso (sourceActionComponentInclusion G S component) := by
  let terminalObject : Over S := Over.mk (𝟙 S)
  have terminalConnected :
      IsConnected terminalObject :=
    sourceGaloisCategory_equivalence_terminal_isConnected
      equivalence terminalObject Over.mkIdTerminal
  let componentObject : Over S :=
    Over.mk (sourceActionComponentInclusion G S component)
  let componentInclusion : componentObject ⟶ terminalObject :=
    Over.homMk (sourceActionComponentInclusion G S component)
      (by simp [componentObject, terminalObject])
  haveI : Mono (sourceActionComponentInclusion G S component) := by
    apply Functor.mono_of_mono_map (continuousActionInclusion G)
    apply Functor.mono_of_mono_map (Action.forget FintypeCat G)
    apply ConcreteCategory.mono_of_injective
    exact Subtype.val_injective
  haveI : Mono componentInclusion := by
    letI : Mono componentInclusion.left := by
      change Mono (sourceActionComponentInclusion G S component)
      infer_instance
    exact Over.mono_of_mono_left componentInclusion
  haveI : IsIso componentInclusion :=
    terminalConnected.noTrivialComponent
      componentObject componentInclusion
      (sourceActionComponentOver_notInitial G S component)
  change IsIso ((Over.forget S).map componentInclusion)
  infer_instance

/-- Equivalence of the slice with a connected anabelioid forces the slicing
action to be nonempty. -/
theorem sourceSlice_equivalentToGalois_implies_nonempty
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    {C : Type (u + 1)} [Category.{u} C] [GaloisCategory C]
    (equivalence : C ≌ Over S) :
    Nonempty S.obj.V := by
  let terminalObject : Over S := Over.mk (𝟙 S)
  have terminalConnected :
      IsConnected terminalObject :=
    sourceGaloisCategory_equivalence_terminal_isConnected
      equivalence terminalObject Over.mkIdTerminal
  by_contra empty
  have emptyFiber : IsEmpty ((continuousActionFiber G).obj S) :=
    not_nonempty_iff.mp empty
  obtain ⟨initialS⟩ :=
    (initial_iff_fiber_empty (continuousActionFiber G) S).mpr emptyFiber
  letI : ∀ T : Over S, Unique (terminalObject ⟶ T) :=
    fun T =>
      { default :=
          Over.homMk (initialS.to T.left)
            (by apply initialS.hom_ext)
        uniq := fun morphism => by
          apply Over.OverMorphism.ext
          apply initialS.hom_ext }
  exact terminalConnected.notInitial
    (IsInitial.ofUnique terminalObject)

/-- If the slice of a finite continuous action is equivalent to a connected
anabelioid, then the action is transitive. -/
theorem sourceSlice_equivalentToGalois_implies_pretransitive
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    {C : Type (u + 1)} [Category.{u} C] [GaloisCategory C]
    (equivalence : C ≌ Over S) :
    MulAction.IsPretransitive G S.obj.V := by
  constructor
  intro first second
  let component : SourceActionComponent G S := Quotient.mk'' first
  haveI : IsIso (sourceActionComponentInclusion G S component) := by
    exact
      sourceActionComponentInclusion_isIso_of_equivalentToGalois
        G S equivalence component
  have inclusionSurjective :
      Function.Surjective
        ((continuousActionFiber G).map
          (sourceActionComponentInclusion G S component)) :=
    ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).surjective
  obtain ⟨secondInComponent, secondEquality⟩ :=
    inclusionSurjective second
  let firstInComponent : SourceActionComponentFiber G S component :=
    ⟨first, rfl⟩
  obtain ⟨g, orbitEquality⟩ :=
    (sourceActionComponentAction_pretransitive G S component
      ).exists_smul_eq firstInComponent secondInComponent
  refine ⟨g, ?_⟩
  change g • first = second
  calc
    g • first = (g • firstInComponent).1 := rfl
    _ = secondInComponent.1 := congrArg Subtype.val orbitEquality
    _ = second := secondEquality

/-! ## Product functors under a change of slicing object -/

/-- Product with a slicing object is natural under an isomorphism of slicing
objects. -/
noncomputable def sourceSliceProductMapIso
    (G : ProfiniteGrp.{u})
    {S T : ContAction FintypeCat.{u} G} (iso : S ≅ T) :
    Over.star S ⋙ (Over.mapIso iso).functor ≅ Over.star T :=
  NatIso.ofComponents
    (fun X =>
      Over.isoMk
        (Limits.prod.mapIso iso (Iso.refl X))
        (by
          dsimp
          rw [Category.assoc, Limits.prod.lift_fst,
            Limits.prod.map_fst]
          rw [← Category.assoc, Limits.prod.lift_fst]))
    (fun f => by
      ext
      simp)

/-! ## Application to the finite-etale factorization -/

namespace SourceFiniteEtaleFunctorFactorization

variable
    {G : ProfiniteGrp.{u}}
    {D : Type (u + 1)} [Category.{u} D] [GaloisCategory D]
    {pullback : ContAction FintypeCat.{u} G ⥤ D}

/-- The slicing action in a connected finite-etale factorization is
nonempty. -/
theorem connectedObjectNonempty
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    Nonempty factorization.object.obj.V :=
  sourceSlice_equivalentToGalois_implies_nonempty
    G factorization.object factorization.sliceEquivalence

/-- The slicing action in a connected finite-etale factorization is
transitive. -/
theorem connectedObjectPretransitive
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    MulAction.IsPretransitive G factorization.object.obj.V :=
  sourceSlice_equivalentToGalois_implies_pretransitive
    G factorization.object factorization.sliceEquivalence

/-- The orbit component selected by a point of the connected slicing
action. -/
noncomputable def connectedObjectComponent
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    SourceActionComponent G factorization.object :=
  Quotient.mk'' (Classical.choice factorization.connectedObjectNonempty)

/-- The open subgroup recovered as the stabilizer of the connected slicing
action. -/
noncomputable def connectedObjectOpenStabilizer
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    OpenSubgroup G :=
  sourceActionComponentOpenStabilizer
    G factorization.object factorization.connectedObjectComponent

/-- The connected slicing action is the coset action of its recovered open
stabilizer. -/
noncomputable def connectedObjectCosetActionIso
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    factorization.object ≅
      sourceOpenCosetAction G factorization.connectedObjectOpenStabilizer := by
  let component := factorization.connectedObjectComponent
  letI :
      IsIso
        (sourceActionComponentInclusion
          G factorization.object component) :=
    sourceActionComponentInclusion_isIso_of_equivalentToGalois
      G factorization.object factorization.sliceEquivalence component
  exact
    (asIso
      (sourceActionComponentInclusion
        G factorization.object component)).symm ≪≫
      sourceActionComponentCosetActionIso
        G factorization.object component

/-- The connected slice is the anabelioid of finite continuous actions of
the recovered open stabilizer. -/
noncomputable def connectedSliceEquivalence
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    Over factorization.object ≌
      ContAction FintypeCat.{u}
        factorization.connectedObjectOpenStabilizer :=
  (Over.mapIso factorization.connectedObjectCosetActionIso).trans
    (sourceOpenCosetSliceEquivalence
      G factorization.connectedObjectOpenStabilizer).symm

/-- The source anabelioid of a connected finite-etale factorization is
equivalent to `B(H)` for the recovered open stabilizer `H`. -/
noncomputable def connectedSourceEquivalence
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    D ≌
      ContAction FintypeCat.{u}
        factorization.connectedObjectOpenStabilizer :=
  factorization.sliceEquivalence.trans
    factorization.connectedSliceEquivalence

/-- Under the derived equivalence of the source with `B(H)`, the original
finite-etale pullback functor is naturally isomorphic to restriction along
the recovered open subgroup `H ≤ G`. -/
noncomputable def connectedSourcePullbackIsoRestriction
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    pullback ⋙ factorization.connectedSourceEquivalence.functor ≅
      sourceOpenSubgroupRestriction
        G factorization.connectedObjectOpenStabilizer := by
  let slice := factorization.sliceEquivalence
  let connectedSlice := factorization.connectedSliceEquivalence
  let objectIso := factorization.connectedObjectCosetActionIso
  let H := factorization.connectedObjectOpenStabilizer
  let cancelSlice :
      slice.inverse ⋙ (slice.functor ⋙ connectedSlice.functor) ≅
        connectedSlice.functor :=
    (Functor.associator
      slice.inverse slice.functor connectedSlice.functor).symm ≪≫
      Functor.isoWhiskerRight
        slice.counitIso connectedSlice.functor ≪≫
      Functor.leftUnitor connectedSlice.functor
  let factorizationTransport :
      pullback ⋙ (slice.functor ⋙ connectedSlice.functor) ≅
        Over.star factorization.object ⋙ connectedSlice.functor :=
    Functor.isoWhiskerRight factorization.pullbackIso
        (slice.functor ⋙ connectedSlice.functor) ≪≫
      Functor.associator
        (Over.star factorization.object)
        slice.inverse
        (slice.functor ⋙ connectedSlice.functor) ≪≫
      Functor.isoWhiskerLeft
        (Over.star factorization.object) cancelSlice
  let changeSlicingObject :
      Over.star factorization.object ⋙ connectedSlice.functor ≅
        Over.star (sourceOpenCosetAction G H) ⋙
          sourceSliceFiberFunctor G H :=
    (Functor.associator
      (Over.star factorization.object)
      (Over.mapIso objectIso).functor
      (sourceSliceFiberFunctor G H)).symm ≪≫
      Functor.isoWhiskerRight
        (sourceSliceProductMapIso G objectIso)
        (sourceSliceFiberFunctor G H)
  change
    pullback ⋙ (slice.functor ⋙ connectedSlice.functor) ≅
      sourceOpenSubgroupRestriction G H
  exact
    factorizationTransport ≪≫
      changeSlicingObject ≪≫
      (sourceOpenSubgroupRestrictionSliceIso G H).symm

end SourceFiniteEtaleFunctorFactorization

end Iut
