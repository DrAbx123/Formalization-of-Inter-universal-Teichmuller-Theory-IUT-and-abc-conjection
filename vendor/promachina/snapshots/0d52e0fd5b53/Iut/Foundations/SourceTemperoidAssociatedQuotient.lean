/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTemperoid

/-!
# Associated quotients of countable continuous actions

Let a group `Deck` act by automorphisms on a countable continuous
`Local`-action `source`.  For a countable `Deck`-action `X`, this file
constructs the associated `Local`-action

`(source × X) / Deck`.

The two actions commute because every deck transformation is a morphism of
`Local`-actions.  This is the carrier-level descent construction used in the
quotient proof of *Semi-graphs of Anabelioids*, Proposition 3.6(ii).
-/

namespace Iut

universe u

open CategoryTheory
open scoped SourceCountableTypeCatDiscrete

namespace SourceTemperoidAssociatedQuotient

variable {Local Deck : Type u}
variable [Group Local] [TopologicalSpace Local] [IsTopologicalGroup Local]
variable [Group Deck]

/-- The action on a local constituent induced by a homomorphism to its
categorical automorphism group. -/
@[reducible]
noncomputable def sourceDeckMulAction
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source) :
    MulAction Deck source.obj.V.obj where
  smul transformation point :=
    (deckAction transformation).hom.hom.hom point
  one_smul point := by
    change (deckAction 1).hom.hom.hom point = point
    rw [map_one]
    rfl
  mul_smul first second point := by
    change (deckAction (first * second)).hom.hom.hom point =
      (deckAction first).hom.hom.hom
        ((deckAction second).hom.hom.hom point)
    rw [map_mul, Aut.Aut_mul_def]
    rfl

/-- Diagonal deck action on a constituent point and an auxiliary deck-set. -/
@[reducible]
noncomputable def diagonalMulAction
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] :
    MulAction Deck (source.obj.V.obj × X) := by
  letI := sourceDeckMulAction source deckAction
  exact inferInstance

/-- Carrier of the associated quotient `(source × X) / Deck`. -/
noncomputable abbrev Carrier
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] :=
  @MulAction.orbitRel.Quotient Deck (source.obj.V.obj × X) _
    (diagonalMulAction source deckAction X)

noncomputable instance carrierCountable
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] [Countable X] :
    Countable (Carrier source deckAction X) :=
  inferInstance

/-- The associated quotient carries the discrete topology required by the
countable temperoid. -/
noncomputable instance carrierTopologicalSpace
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] :
    TopologicalSpace (Carrier source deckAction X) := ⊥

noncomputable instance carrierDiscreteTopology
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] :
    DiscreteTopology (Carrier source deckAction X) :=
  ⟨rfl⟩

/-- Insert a pair into its diagonal deck orbit. -/
noncomputable def mk
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X]
    (point : source.obj.V.obj × X) : Carrier source deckAction X := by
  letI := diagonalMulAction source deckAction X
  exact Quotient.mk'' point

/-- Acting diagonally does not change the associated quotient class. -/
theorem mk_smul
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X]
    (transformation : Deck) (point : source.obj.V.obj × X) :
    mk source deckAction
        ((deckAction transformation).hom.hom.hom point.1,
          transformation • point.2) =
      mk source deckAction point := by
  letI := diagonalMulAction source deckAction X
  exact Quotient.sound (MulAction.mem_orbit _ transformation)

/-- Forget the source coordinate of an associated-quotient class, retaining
only the deck orbit of its auxiliary coordinate.  Diagonal equivalence makes
this independent of the chosen representative. -/
noncomputable def auxiliaryComponent
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] :
    Carrier source deckAction X → MulAction.orbitRel.Quotient Deck X := by
  letI := diagonalMulAction source deckAction X
  exact Quotient.map' Prod.snd (by
    intro first second related
    rw [MulAction.orbitRel_apply] at related ⊢
    obtain ⟨transformation, equality⟩ :=
      MulAction.mem_orbit_iff.mp related
    exact MulAction.mem_orbit_iff.mpr
      ⟨transformation, congrArg Prod.snd equality⟩)

@[simp]
theorem auxiliaryComponent_mk
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X]
    (point : source.obj.V.obj × X) :
    auxiliaryComponent source deckAction X (mk source deckAction point) =
      Quotient.mk'' point.2 :=
  rfl

/-- The local group acts on diagonal deck orbits through the first
coordinate. -/
@[reducible]
noncomputable def localMulAction
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] :
    MulAction Local (Carrier source deckAction X) where
  smul element point := by
    letI := diagonalMulAction source deckAction X
    exact Quotient.map' (fun pair ↦ (element • pair.1, pair.2)) (by
      intro first second related
      rw [MulAction.orbitRel_apply] at related ⊢
      obtain ⟨transformation, equality⟩ :=
        MulAction.mem_orbit_iff.mp related
      refine MulAction.mem_orbit_iff.mpr ⟨transformation, ?_⟩
      rw [← equality]
      apply Prod.ext
      · exact ConcreteCategory.congr_hom
          ((deckAction transformation).hom.hom.comm element) second.1
      · rfl) point
  one_smul point := by
    letI := diagonalMulAction source deckAction X
    induction point using Quotient.inductionOn' with
    | _ point =>
        apply congrArg Quotient.mk''
        exact Prod.ext (one_smul Local point.1) rfl
  mul_smul first second point := by
    letI := diagonalMulAction source deckAction X
    induction point using Quotient.inductionOn' with
    | _ point =>
        apply congrArg Quotient.mk''
        exact Prod.ext (mul_smul first second point.1) rfl

/-- Formula for the local action on a represented associated-quotient class. -/
@[simp]
theorem local_smul_mk
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X]
    (element : Local) (point : source.obj.V.obj × X) :
    letI := localMulAction source deckAction X
    element • mk source deckAction point =
      mk source deckAction (element • point.1, point.2) :=
  rfl

/-- Local constituent motion does not change the auxiliary deck orbit. -/
theorem auxiliaryComponent_local_smul
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X]
    (element : Local) (point : Carrier source deckAction X) :
    letI := localMulAction source deckAction X
    auxiliaryComponent source deckAction X (element • point) =
      auxiliaryComponent source deckAction X point := by
  letI := localMulAction source deckAction X
  letI := diagonalMulAction source deckAction X
  induction point using Quotient.inductionOn' with
  | _ point => rfl

/-- The associated quotient is a continuous local action.  Continuity is
controlled by the open stabilizer of the represented constituent point. -/
theorem continuous_localSMul
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] :
    letI := localMulAction source deckAction X
    ContinuousSMul Local (Carrier source deckAction X) := by
  letI := localMulAction source deckAction X
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro orbit
  letI := diagonalMulAction source deckAction X
  induction orbit using Quotient.inductionOn' with
  | _ point =>
      apply Subgroup.isOpen_mono
        (H₁ := MulAction.stabilizer Local point.1)
        (H₂ := MulAction.stabilizer Local (Quotient.mk'' point))
      · intro element fixes
        rw [MulAction.mem_stabilizer_iff] at fixes ⊢
        apply congrArg Quotient.mk''
        exact Prod.ext fixes rfl
      · exact stabilizer_isOpen Local point.1

/-- The associated quotient as an object of the local temperoid. -/
noncomputable def action
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] [Countable X] :
    SourceTemperoidAction Local := by
  letI := localMulAction source deckAction X
  exact ⟨SourceCountableTypeCat.ofMulAction Local
      (SourceCountableTypeCat.of (Carrier source deckAction X)),
    continuous_localSMul source deckAction X⟩

@[simp]
theorem action_smul_mk
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (X : Type u) [MulAction Deck X] [Countable X]
    (element : Local) (point : source.obj.V.obj × X) :
    ConcreteCategory.hom ((action source deckAction X).obj.ρ element)
        (mk source deckAction point) =
      mk source deckAction (element • point.1, point.2) :=
  rfl

/-- Fixing one auxiliary point gives the structural map from the source
action to its associated quotient.  Geometrically this is the map from the
universal cover to the corresponding intermediate quotient. -/
noncomputable def insertion
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X] [Countable X]
    (point : X) :
    source ⟶ action source deckAction X :=
  ObjectProperty.homMk
    { hom := SourceCountableTypeCat.homMk
        (fun sourcePoint ↦ mk source deckAction (sourcePoint, point))
      comm := fun element ↦ by
        apply ConcreteCategory.hom_ext
        intro sourcePoint
        exact (local_smul_mk source deckAction X element
          (sourcePoint, point)).symm }

@[simp]
theorem insertion_apply
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X] [Countable X]
    (point : X) (sourcePoint : source.obj.V.obj) :
    (insertion source deckAction point).hom.hom sourcePoint =
      mk source deckAction (sourcePoint, point) :=
  rfl

/-- When the auxiliary deck action is transitive, the structural map from
the source action onto its associated quotient is surjective. -/
theorem insertion_surjective
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X] [Countable X]
    (point : X) (transitive : MulAction.IsPretransitive Deck X) :
    Function.Surjective
      (insertion source deckAction point).hom.hom := by
  intro targetPoint
  letI := diagonalMulAction source deckAction X
  induction targetPoint using Quotient.inductionOn' with
  | _ targetPoint =>
      obtain ⟨transformation, auxiliaryEquality⟩ :=
        transitive.exists_smul_eq point targetPoint.2
      let sourcePoint :=
        (deckAction transformation⁻¹).hom.hom.hom targetPoint.1
      refine ⟨sourcePoint, ?_⟩
      change mk source deckAction (sourcePoint, point) =
        mk source deckAction targetPoint
      have orbitEquality := mk_smul source deckAction transformation
        (sourcePoint, point)
      rw [auxiliaryEquality] at orbitEquality
      have sourceEquality :
          (deckAction transformation).hom.hom.hom sourcePoint =
            targetPoint.1 := by
        change (deckAction transformation).hom.hom.hom
            ((deckAction transformation⁻¹).hom.hom.hom targetPoint.1) =
          targetPoint.1
        rw [map_inv]
        exact (deckAction transformation).inv_hom_id_apply targetPoint.1
      rw [sourceEquality] at orbitEquality
      exact orbitEquality.symm

/-! ## Normalization over a deck torsor -/

/-- Insert an auxiliary point over a chosen point of the source action. -/
noncomputable def baseInsertion
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X]
    (basePoint : source.obj.V.obj) (point : X) :
    Carrier source deckAction X :=
  mk source deckAction (basePoint, point)

/-- Freeness of the source deck action makes insertion over a fixed source
point injective. -/
theorem baseInsertion_injective
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X]
    (basePoint : source.obj.V.obj)
    (free : letI := sourceDeckMulAction source deckAction;
      IsCancelSMul Deck source.obj.V.obj) :
    Function.Injective (baseInsertion source deckAction basePoint (X := X)) := by
  letI := sourceDeckMulAction source deckAction
  letI : IsCancelSMul Deck source.obj.V.obj := free
  intro first second equality
  letI := diagonalMulAction source deckAction X
  have related := Quotient.exact equality
  change (basePoint, first) ∈
    MulAction.orbit Deck (basePoint, second) at related
  obtain ⟨transformation, orbitEquality⟩ :=
    MulAction.mem_orbit_iff.mp related
  have fixesBase : transformation • basePoint = basePoint :=
    congrArg Prod.fst orbitEquality
  have transformationOne : transformation = 1 :=
    IsCancelSMul.eq_one_of_smul fixesBase
  subst transformation
  have fiberEquality := congrArg Prod.snd orbitEquality
  simpa using fiberEquality.symm

/-- Transitivity of the source deck action lets every associated-quotient
class be represented uniquely over a chosen source point. -/
theorem baseInsertion_surjective
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X]
    (basePoint : source.obj.V.obj)
    (transitive : letI := sourceDeckMulAction source deckAction;
      MulAction.IsPretransitive Deck source.obj.V.obj) :
    Function.Surjective
      (baseInsertion source deckAction basePoint (X := X)) := by
  letI := sourceDeckMulAction source deckAction
  letI : MulAction.IsPretransitive Deck source.obj.V.obj := transitive
  intro orbit
  letI := diagonalMulAction source deckAction X
  induction orbit using Quotient.inductionOn' with
  | _ point =>
      obtain ⟨transformation, sourceEquality⟩ :=
        MulAction.exists_smul_eq Deck point.1 basePoint
      change (deckAction transformation).hom.hom.hom point.1 =
        basePoint at sourceEquality
      refine ⟨transformation • point.2, ?_⟩
      change mk source deckAction
          (basePoint, transformation • point.2) =
        mk source deckAction point
      rw [← sourceEquality]
      exact mk_smul source deckAction transformation point

/-- If the source is a deck torsor, normalization at a chosen source point
identifies its associated quotient carrier with the auxiliary deck-set. -/
noncomputable def baseInsertionEquiv
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X]
    (basePoint : source.obj.V.obj)
    (free : letI := sourceDeckMulAction source deckAction;
      IsCancelSMul Deck source.obj.V.obj)
    (transitive : letI := sourceDeckMulAction source deckAction;
      MulAction.IsPretransitive Deck source.obj.V.obj) :
    X ≃ Carrier source deckAction X :=
  Equiv.ofBijective (baseInsertion source deckAction basePoint)
    ⟨baseInsertion_injective source deckAction basePoint free,
      baseInsertion_surjective source deckAction basePoint transitive⟩

@[simp]
theorem baseInsertionEquiv_apply
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    {X : Type u} [MulAction Deck X]
    (basePoint : source.obj.V.obj)
    (free : letI := sourceDeckMulAction source deckAction;
      IsCancelSMul Deck source.obj.V.obj)
    (transitive : letI := sourceDeckMulAction source deckAction;
      MulAction.IsPretransitive Deck source.obj.V.obj)
    (point : X) :
    baseInsertionEquiv source deckAction basePoint free transitive point =
      mk source deckAction (basePoint, point) :=
  rfl

section SourceFunctoriality

/-- A morphism between deck-equivariant local actions descends to their
associated quotients when it commutes with every deck transformation. -/
noncomputable def sourceFiberMap
    {source target : SourceTemperoidAction Local}
    (sourceDeckAction : Deck →* Aut source)
    (targetDeckAction : Deck →* Aut target)
    {X : Type u} [MulAction Deck X]
    (map : source ⟶ target)
    (commutes : ∀ transformation,
      (sourceDeckAction transformation).hom ≫ map =
        map ≫ (targetDeckAction transformation).hom) :
    Carrier source sourceDeckAction X →
      Carrier target targetDeckAction X := by
  letI := diagonalMulAction source sourceDeckAction X
  letI := diagonalMulAction target targetDeckAction X
  exact Quotient.map' (fun point ↦ (map.hom.hom point.1, point.2)) (by
    intro first second related
    rw [MulAction.orbitRel_apply] at related ⊢
    obtain ⟨transformation, equality⟩ :=
      MulAction.mem_orbit_iff.mp related
    refine MulAction.mem_orbit_iff.mpr ⟨transformation, ?_⟩
    rw [← equality]
    apply Prod.ext
    · exact (ConcreteCategory.congr_hom
        (congrArg (fun arrow ↦ arrow.hom.hom)
          (commutes transformation)) second.1).symm
    · rfl)

@[simp]
theorem sourceFiberMap_mk
    {source target : SourceTemperoidAction Local}
    (sourceDeckAction : Deck →* Aut source)
    (targetDeckAction : Deck →* Aut target)
    {X : Type u} [MulAction Deck X]
    (map : source ⟶ target)
    (commutes : ∀ transformation,
      (sourceDeckAction transformation).hom ≫ map =
        map ≫ (targetDeckAction transformation).hom)
    (point : source.obj.V.obj × X) :
    sourceFiberMap sourceDeckAction targetDeckAction map commutes
        (mk source sourceDeckAction point) =
      mk target targetDeckAction (map.hom.hom point.1, point.2) :=
  rfl

/-- The morphism of associated local actions induced by an equivariant map
of their source actions. -/
noncomputable def sourceMap
    {source target : SourceTemperoidAction Local}
    (sourceDeckAction : Deck →* Aut source)
    (targetDeckAction : Deck →* Aut target)
    {X : Type u} [MulAction Deck X] [Countable X]
    (map : source ⟶ target)
    (commutes : ∀ transformation,
      (sourceDeckAction transformation).hom ≫ map =
        map ≫ (targetDeckAction transformation).hom) :
    action source sourceDeckAction X ⟶
      action target targetDeckAction X :=
  ObjectProperty.homMk
    ({ hom := SourceCountableTypeCat.homMk
          (sourceFiberMap sourceDeckAction targetDeckAction map commutes)
       comm := fun element ↦ by
         apply ConcreteCategory.hom_ext
         intro point
         letI := diagonalMulAction source sourceDeckAction X
         induction point using Quotient.inductionOn' with
         | _ point =>
             apply congrArg (mk target targetDeckAction)
             exact Prod.ext
               (ConcreteCategory.congr_hom (map.hom.comm element) point.1)
               rfl } :
      (action source sourceDeckAction X).obj ⟶
      (action target targetDeckAction X).obj)

section DeckTransition

variable {FinerDeck : Type u} [Group FinerDeck]

/-- A map of source actions equivariant along a deck-group transition
descends to associated quotients.  The auxiliary `Deck`-action on `X` is
restricted along `transition` on the source side. -/
noncomputable def sourceFiberMapOfTransition
    {source target : SourceTemperoidAction Local}
    (sourceDeckAction : FinerDeck →* Aut source)
    (targetDeckAction : Deck →* Aut target)
    (transition : FinerDeck →* Deck)
    {X : Type u} [MulAction Deck X]
    (map : source ⟶ target)
    (commutes : ∀ transformation,
      (sourceDeckAction transformation).hom ≫ map =
        map ≫ (targetDeckAction (transition transformation)).hom) :
    @Carrier Local FinerDeck _ _ _ _ source sourceDeckAction X
        (MulAction.compHom X transition) →
      Carrier target targetDeckAction X := by
  letI : MulAction FinerDeck X := MulAction.compHom X transition
  letI := diagonalMulAction source sourceDeckAction X
  letI := diagonalMulAction target targetDeckAction X
  exact Quotient.map' (fun point ↦ (map.hom.hom point.1, point.2)) (by
    intro first second related
    rw [MulAction.orbitRel_apply] at related ⊢
    obtain ⟨transformation, equality⟩ :=
      MulAction.mem_orbit_iff.mp related
    refine MulAction.mem_orbit_iff.mpr ⟨transition transformation, ?_⟩
    rw [← equality]
    apply Prod.ext
    · exact (ConcreteCategory.congr_hom
        (congrArg (fun arrow ↦ arrow.hom.hom)
          (commutes transformation)) second.1).symm
    · rfl)

@[simp]
theorem sourceFiberMapOfTransition_mk
    {source target : SourceTemperoidAction Local}
    (sourceDeckAction : FinerDeck →* Aut source)
    (targetDeckAction : Deck →* Aut target)
    (transition : FinerDeck →* Deck)
    {X : Type u} [MulAction Deck X]
    (map : source ⟶ target)
    (commutes : ∀ transformation,
      (sourceDeckAction transformation).hom ≫ map =
        map ≫ (targetDeckAction (transition transformation)).hom)
    (point : source.obj.V.obj × X) :
    sourceFiberMapOfTransition sourceDeckAction targetDeckAction transition
        map commutes
        (@mk Local FinerDeck _ _ _ _ source sourceDeckAction X
          (MulAction.compHom X transition) point) =
      mk target targetDeckAction (map.hom.hom point.1, point.2) :=
  rfl

/-- The local-action morphism induced by an equivariant source map along a
deck-group transition. -/
noncomputable def sourceMapOfTransition
    {source target : SourceTemperoidAction Local}
    (sourceDeckAction : FinerDeck →* Aut source)
    (targetDeckAction : Deck →* Aut target)
    (transition : FinerDeck →* Deck)
    {X : Type u} [MulAction Deck X] [Countable X]
    (map : source ⟶ target)
    (commutes : ∀ transformation,
      (sourceDeckAction transformation).hom ≫ map =
        map ≫ (targetDeckAction (transition transformation)).hom) :
    @action Local FinerDeck _ _ _ _ source sourceDeckAction X
        (MulAction.compHom X transition) _ ⟶
      action target targetDeckAction X :=
  ObjectProperty.homMk
    ({ hom := SourceCountableTypeCat.homMk
          (sourceFiberMapOfTransition sourceDeckAction targetDeckAction
            transition map commutes)
       comm := fun element ↦ by
         apply ConcreteCategory.hom_ext
         intro point
         letI : MulAction FinerDeck X := MulAction.compHom X transition
         letI := diagonalMulAction source sourceDeckAction X
         induction point using Quotient.inductionOn' with
         | _ point =>
             apply congrArg (mk target targetDeckAction)
             exact Prod.ext
               (ConcreteCategory.congr_hom (map.hom.comm element) point.1)
               rfl } :
      (@action Local FinerDeck _ _ _ _ source sourceDeckAction X
        (MulAction.compHom X transition) _).obj ⟶
        (action target targetDeckAction X).obj)

@[simp]
theorem sourceMapOfTransition_mk
    {source target : SourceTemperoidAction Local}
    (sourceDeckAction : FinerDeck →* Aut source)
    (targetDeckAction : Deck →* Aut target)
    (transition : FinerDeck →* Deck)
    {X : Type u} [MulAction Deck X] [Countable X]
    (map : source ⟶ target)
    (commutes : ∀ transformation,
      (sourceDeckAction transformation).hom ≫ map =
        map ≫ (targetDeckAction (transition transformation)).hom)
    (point : source.obj.V.obj × X) :
    (sourceMapOfTransition sourceDeckAction targetDeckAction transition
      map commutes).hom.hom
        (@mk Local FinerDeck _ _ _ _ source sourceDeckAction X
          (MulAction.compHom X transition) point) =
      mk target targetDeckAction (map.hom.hom point.1, point.2) :=
  rfl

end DeckTransition

@[simp]
theorem sourceMap_mk
    {source target : SourceTemperoidAction Local}
    (sourceDeckAction : Deck →* Aut source)
    (targetDeckAction : Deck →* Aut target)
    {X : Type u} [MulAction Deck X] [Countable X]
    (map : source ⟶ target)
    (commutes : ∀ transformation,
      (sourceDeckAction transformation).hom ≫ map =
        map ≫ (targetDeckAction transformation).hom)
    (point : source.obj.V.obj × X) :
    (sourceMap sourceDeckAction targetDeckAction map commutes).hom.hom
        (mk source sourceDeckAction point) =
      mk target targetDeckAction (map.hom.hom point.1, point.2) :=
  rfl

/-- Commutation of an isomorphism with deck actions automatically gives the
corresponding commutation law for its inverse. -/
theorem sourceIso_invCommutes
    {source target : SourceTemperoidAction Local}
    (sourceDeckAction : Deck →* Aut source)
    (targetDeckAction : Deck →* Aut target)
    (identification : source ≅ target)
    (homCommutes : ∀ transformation,
      (sourceDeckAction transformation).hom ≫ identification.hom =
        identification.hom ≫ (targetDeckAction transformation).hom)
    (transformation : Deck) :
    (targetDeckAction transformation).hom ≫ identification.inv =
      identification.inv ≫ (sourceDeckAction transformation).hom := by
  rw [← cancel_mono identification.hom]
  simp only [Category.assoc]
  rw [← Category.assoc, homCommutes]
  simp

/-- A deck-equivariant isomorphism of local actions descends to an
isomorphism of associated quotients. -/
noncomputable def sourceIso
    {source target : SourceTemperoidAction Local}
    (sourceDeckAction : Deck →* Aut source)
    (targetDeckAction : Deck →* Aut target)
    {X : Type u} [MulAction Deck X] [Countable X]
    (identification : source ≅ target)
    (homCommutes : ∀ transformation,
      (sourceDeckAction transformation).hom ≫ identification.hom =
        identification.hom ≫ (targetDeckAction transformation).hom)
    (invCommutes : ∀ transformation,
      (targetDeckAction transformation).hom ≫ identification.inv =
        identification.inv ≫ (sourceDeckAction transformation).hom) :
    action source sourceDeckAction X ≅
      action target targetDeckAction X where
  hom := sourceMap sourceDeckAction targetDeckAction
    identification.hom homCommutes
  inv := sourceMap targetDeckAction sourceDeckAction
    identification.inv invCommutes
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    letI := diagonalMulAction source sourceDeckAction X
    induction point using Quotient.inductionOn' with
    | _ point =>
        apply congrArg (mk source sourceDeckAction)
        exact Prod.ext
          (congrArg (fun arrow ↦ arrow.hom.hom point.1)
            identification.hom_inv_id)
          rfl
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    letI := diagonalMulAction target targetDeckAction X
    induction point using Quotient.inductionOn' with
    | _ point =>
        apply congrArg (mk target targetDeckAction)
        exact Prod.ext
          (congrArg (fun arrow ↦ arrow.hom.hom point.1)
            identification.inv_hom_id)
          rfl

/-- Version of `sourceIso` requiring only the forward commutation square. -/
noncomputable def sourceIsoOfHomCommutes
    {source target : SourceTemperoidAction Local}
    (sourceDeckAction : Deck →* Aut source)
    (targetDeckAction : Deck →* Aut target)
    {X : Type u} [MulAction Deck X] [Countable X]
    (identification : source ≅ target)
    (homCommutes : ∀ transformation,
      (sourceDeckAction transformation).hom ≫ identification.hom =
        identification.hom ≫ (targetDeckAction transformation).hom) :
    action source sourceDeckAction X ≅
      action target targetDeckAction X :=
  sourceIso sourceDeckAction targetDeckAction identification homCommutes
    (sourceIso_invCommutes sourceDeckAction targetDeckAction
      identification homCommutes)

end SourceFunctoriality

section Functoriality

variable [TopologicalSpace Deck] [IsTopologicalGroup Deck]

/-- An equivariant map of auxiliary deck-actions descends on associated
quotients. -/
noncomputable def fiberMap
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    {X Y : SourceTemperoidAction Deck} (map : X ⟶ Y) :
    Carrier source deckAction X.obj.V.obj →
      Carrier source deckAction Y.obj.V.obj := by
  letI := diagonalMulAction source deckAction X.obj.V.obj
  letI := diagonalMulAction source deckAction Y.obj.V.obj
  exact Quotient.map' (fun point ↦ (point.1, map.hom.hom point.2)) (by
    intro first second related
    rw [MulAction.orbitRel_apply] at related ⊢
    obtain ⟨transformation, equality⟩ :=
      MulAction.mem_orbit_iff.mp related
    refine MulAction.mem_orbit_iff.mpr ⟨transformation, ?_⟩
    rw [← equality]
    apply Prod.ext
    · rfl
    · exact (ConcreteCategory.congr_hom
        (map.hom.comm transformation) second.2).symm)

@[simp]
theorem fiberMap_mk
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    {X Y : SourceTemperoidAction Deck} (map : X ⟶ Y)
    (point : source.obj.V.obj × X.obj.V.obj) :
    fiberMap source deckAction map (mk source deckAction point) =
      mk source deckAction (point.1, map.hom.hom point.2) :=
  rfl

/-- The morphism of associated local actions induced by a morphism of
auxiliary deck-actions. -/
noncomputable def map
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    {X Y : SourceTemperoidAction Deck} (arrow : X ⟶ Y) :
    action source deckAction X.obj.V.obj ⟶
      action source deckAction Y.obj.V.obj :=
  ObjectProperty.homMk
    ({ hom := SourceCountableTypeCat.homMk
          (fiberMap source deckAction arrow)
       comm := fun element ↦ by
         apply ConcreteCategory.hom_ext
         intro point
         letI := diagonalMulAction source deckAction X.obj.V.obj
         induction point using Quotient.inductionOn' with
         | _ point => rfl } :
      (action source deckAction X.obj.V.obj).obj ⟶
        (action source deckAction Y.obj.V.obj).obj)

/-- Associated quotient as a functor in the auxiliary deck-action. -/
noncomputable def functor
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source) :
    SourceTemperoidAction Deck ⥤ SourceTemperoidAction Local where
  obj X := action source deckAction X.obj.V.obj
  map := map source deckAction
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    letI := diagonalMulAction source deckAction X.obj.V.obj
    induction point using Quotient.inductionOn' with
    | _ point => rfl
  map_comp {X Y Z} first second := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    letI := diagonalMulAction source deckAction X.obj.V.obj
    induction point using Quotient.inductionOn' with
    | _ point => rfl

/-- A free deck action on the source makes the associated-quotient functor
faithful: evaluating a quotient map on one fixed source point recovers the
auxiliary equivariant map. -/
@[reducible]
noncomputable def functorFaithful
    (source : SourceTemperoidAction Local)
    (deckAction : Deck →* Aut source)
    (basePoint : source.obj.V.obj)
    (free : letI := sourceDeckMulAction source deckAction;
      IsCancelSMul Deck source.obj.V.obj) :
    (functor source deckAction).Faithful where
  map_injective {X Y} first second equality := by
    letI := sourceDeckMulAction source deckAction
    letI : IsCancelSMul Deck source.obj.V.obj := free
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro point
    have atClass := congrArg
      (fun arrow : (functor source deckAction).obj X ⟶
          (functor source deckAction).obj Y ↦
        arrow.hom.hom
          (mk source deckAction (basePoint, point))) equality
    change mk source deckAction (basePoint, first.hom.hom point) =
      mk source deckAction (basePoint, second.hom.hom point) at atClass
    letI := diagonalMulAction source deckAction Y.obj.V.obj
    have related := Quotient.exact atClass
    change (basePoint, first.hom.hom point) ∈
      MulAction.orbit Deck (basePoint, second.hom.hom point) at related
    obtain ⟨transformation, orbitEquality⟩ :=
      MulAction.mem_orbit_iff.mp related
    have fixesBase : transformation • basePoint = basePoint :=
      congrArg Prod.fst orbitEquality
    have transformationOne : transformation = 1 :=
      IsCancelSMul.eq_one_of_smul fixesBase
    subst transformation
    have fiberEquality := congrArg Prod.snd orbitEquality
    simpa using fiberEquality.symm

end Functoriality

end SourceTemperoidAssociatedQuotient

end Iut
