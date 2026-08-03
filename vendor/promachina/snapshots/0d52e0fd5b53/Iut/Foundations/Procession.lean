/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.PNat.Basic

/-!
# Capsules and processions

This module formalizes the categorical conventions in IUT I, Section 0 and
Definition 4.10.  A capsule retains its actual finite index type.  A
capsule-full poly-morphism is determined by a fixed injection of index sets;
its members are *all* collections of component isomorphisms over that
injection.  Procession morphisms use the inhabited such sets, exactly the
case in which full sets are closed under the paper's multiplicity-free
pairwise composition.  A procession has positive length and its `j`-th
capsule has cardinality `j + 1`.
-/

open CategoryTheory
open scoped BigOperators

namespace Iut

universe v u

/-- A finite indexed collection of objects of a category. -/
structure CategoryCapsule (C : CategoryTheory.Cat.{v, u}) where
  index : Type u
  [finiteIndex : Fintype index]
  object : index -> C

attribute [instance] CategoryCapsule.finiteIndex

namespace CategoryCapsule

variable {C : CategoryTheory.Cat.{v, u}}

/-- An ordinary morphism of capsules from the convention in IUT I, Section 0. -/
structure Hom (source target : CategoryCapsule C) where
  indexEmbedding : source.index ↪ target.index
  component :
    ∀ j, source.object j ⟶ target.object (indexEmbedding j)

namespace Hom

variable {source target third : CategoryCapsule C}

@[ext]
theorem ext (f g : Hom source target)
    (indexEmbedding_eq : f.indexEmbedding = g.indexEmbedding)
    (component_eq : HEq f.component g.component) :
    f = g := by
  cases f with
  | mk fEmbedding fComponent =>
    cases g with
    | mk gEmbedding gComponent =>
      cases indexEmbedding_eq
      simp only [heq_eq_eq] at component_eq
      congr

/-- Identity morphism of a capsule. -/
def id (source : CategoryCapsule C) : Hom source source where
  indexEmbedding := Function.Embedding.refl source.index
  component j := 𝟙 (source.object j)

/-- Composition of ordinary capsule morphisms. -/
def comp (f : Hom source target) (g : Hom target third) :
    Hom source third where
  indexEmbedding := f.indexEmbedding.trans g.indexEmbedding
  component j := f.component j ≫ g.component (f.indexEmbedding j)

end Hom

instance : Category (CategoryCapsule C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext
    · rfl
    · apply heq_of_eq
      funext j
      simp [Hom.comp, Hom.id]
  comp_id f := by
    apply Hom.ext
    · rfl
    · apply heq_of_eq
      funext j
      simp [Hom.comp, Hom.id]
  assoc f g h := by
    apply Hom.ext
    · rfl
    · apply heq_of_eq
      funext j
      simp [Hom.comp, Category.assoc]

/-- Apply a functor componentwise to a capsule without changing its index set. -/
def map
    {D : CategoryTheory.Cat.{v, u}}
    (F : C ⥤ D)
    (capsule : CategoryCapsule C) :
    CategoryCapsule D where
  index := capsule.index
  object j := F.obj (capsule.object j)

namespace Hom

variable {D : CategoryTheory.Cat.{v, u}}

/-- Apply a functor to an ordinary capsule morphism. -/
def map
    (F : C ⥤ D)
    {source target : CategoryCapsule C}
    (f : Hom source target) :
    Hom (CategoryCapsule.map F source)
      (CategoryCapsule.map F target) where
  indexEmbedding := f.indexEmbedding
  component j := F.map (f.component j)

end Hom

/--
A capsule-full poly-morphism.

The data is only the fixed injection.  The associated poly-morphism is the
entire type `Members`, i.e. all componentwise isomorphism collections over
that injection.
-/
structure FullPolyMorphism (source target : CategoryCapsule C) where
  indexEmbedding : source.index ↪ target.index

namespace FullPolyMorphism

variable {source target : CategoryCapsule C}

@[ext]
theorem ext (f g : FullPolyMorphism source target)
    (indexEmbedding_eq : f.indexEmbedding = g.indexEmbedding) :
    f = g := by
  cases f
  cases g
  cases indexEmbedding_eq
  rfl

/-- All members of the capsule-full poly-morphism. -/
def Members (f : FullPolyMorphism source target) :=
  ∀ j, source.object j ≅ target.object (f.indexEmbedding j)

/-- A member gives an ordinary capsule morphism. -/
def toHom (f : FullPolyMorphism source target)
    (member : f.Members) : Hom source target where
  indexEmbedding := f.indexEmbedding
  component j := (member j).hom

/--
The capsule-full poly-morphism is a capsule-full poly-isomorphism precisely
when its fixed index injection is also surjective.
-/
def IsPolyIsomorphism (f : FullPolyMorphism source target) : Prop :=
  Function.Surjective f.indexEmbedding

/-- Identity capsule-full poly-morphism. -/
def id (source : CategoryCapsule C) :
    FullPolyMorphism source source where
  indexEmbedding := Function.Embedding.refl source.index

/-- Composition of capsule-full poly-morphisms. -/
def comp {third : CategoryCapsule C}
    (f : FullPolyMorphism source target)
    (g : FullPolyMorphism target third) :
    FullPolyMorphism source third where
  indexEmbedding := f.indexEmbedding.trans g.indexEmbedding

/-- Componentwise composition sends a member of each factor to a member of the composite. -/
def Members.comp {third : CategoryCapsule C}
    {f : FullPolyMorphism source target}
    {g : FullPolyMorphism target third}
    (fMember : f.Members)
    (gMember : g.Members) :
    (f.comp g).Members :=
  fun j => (fMember j).trans (gMember (f.indexEmbedding j))

/--
The paper's multiplicity-free set of pairwise composites of two full-poly
member sets.  `Set.range` forgets how many pairs yield the same composite.
-/
def pairwiseCompositeSet {third : CategoryCapsule C}
    (f : FullPolyMorphism source target)
    (g : FullPolyMorphism target third) :
    Set (f.comp g).Members :=
  Set.range fun members : f.Members × g.Members =>
    members.1.comp members.2

/-- Apply a functor to a capsule-full poly-morphism. -/
def map
    {D : CategoryTheory.Cat.{v, u}}
    (F : C ⥤ D)
    {source target : CategoryCapsule C}
    (f : FullPolyMorphism source target) :
    FullPolyMorphism
      (CategoryCapsule.map F source)
      (CategoryCapsule.map F target) where
  indexEmbedding := f.indexEmbedding

/-- Apply a functor to every isomorphism in a full-poly member. -/
def Members.map
    {D : CategoryTheory.Cat.{v, u}}
    (F : C ⥤ D)
    {source target : CategoryCapsule C}
    {f : FullPolyMorphism source target}
    (member : f.Members) :
    (f.map F).Members :=
  fun j => F.mapIso (member j)

end FullPolyMorphism

/--
A capsule-full poly-morphism whose full member set is inhabited.

This is the source-accurate class of capsule-full poly-morphisms used as
procession arrows: nonemptiness makes the pairwise composite full again.  The
witness is propositionally truncated, so it introduces no distinguished
member into the poly-morphism.
-/
structure InhabitedFullPolyMorphism
    (source target : CategoryCapsule C)
    extends FullPolyMorphism source target where
  members_nonempty : Nonempty toFullPolyMorphism.Members

namespace InhabitedFullPolyMorphism

variable {source middle target : CategoryCapsule C}

/-- The actual full set of componentwise-isomorphism members. -/
abbrev Members
    (morphism : InhabitedFullPolyMorphism source target) :=
  morphism.toFullPolyMorphism.Members

@[ext]
theorem ext
    (first second : InhabitedFullPolyMorphism source target)
    (indexEmbedding_eq :
      first.indexEmbedding = second.indexEmbedding) :
    first = second := by
  cases first with
  | mk firstPoly firstNonempty =>
    cases second with
    | mk secondPoly secondNonempty =>
      have poly_eq : firstPoly = secondPoly :=
        FullPolyMorphism.ext firstPoly secondPoly indexEmbedding_eq
      cases poly_eq
      rfl

/-- The identity full poly-morphism, inhabited by identity isomorphisms. -/
def id (source : CategoryCapsule C) :
    InhabitedFullPolyMorphism source source where
  toFullPolyMorphism := FullPolyMorphism.id source
  members_nonempty := ⟨fun _ => Iso.refl _⟩

/--
Composition retains the composite injection and an existence witness for a
pairwise composite.
-/
def comp
    (first : InhabitedFullPolyMorphism source middle)
    (second : InhabitedFullPolyMorphism middle target) :
    InhabitedFullPolyMorphism source target where
  toFullPolyMorphism :=
    first.toFullPolyMorphism.comp second.toFullPolyMorphism
  members_nonempty := by
    rcases first.members_nonempty with ⟨firstMember⟩
    rcases second.members_nonempty with ⟨secondMember⟩
    exact ⟨firstMember.comp secondMember⟩

/-- Apply a functor without changing the fixed index injection. -/
def map
    {D : CategoryTheory.Cat.{v, u}}
    (F : C ⥤ D)
    {source target : CategoryCapsule C}
    (morphism : InhabitedFullPolyMorphism source target) :
    InhabitedFullPolyMorphism
      (CategoryCapsule.map F source)
      (CategoryCapsule.map F target) where
  toFullPolyMorphism := morphism.toFullPolyMorphism.map F
  members_nonempty := by
    rcases morphism.members_nonempty with ⟨member⟩
    exact ⟨member.map F⟩

/--
Every member of a composite inhabited full poly-morphism factors through one
member of each input.  This is the missing reverse inclusion in the paper's
set-theoretic composition rule.
-/
theorem members_comp_surjective
    (first : InhabitedFullPolyMorphism source middle)
    (second : InhabitedFullPolyMorphism middle target) :
    Function.Surjective
      (fun members : first.Members × second.Members =>
        members.1.comp members.2) := by
  intro compositeMember
  let secondMember : second.Members :=
    Classical.choice second.members_nonempty
  let firstMember : first.Members := fun sourceIndex =>
    (compositeMember sourceIndex).trans
      (secondMember (first.indexEmbedding sourceIndex)).symm
  refine ⟨(firstMember, secondMember), ?_⟩
  funext sourceIndex
  apply Iso.ext
  simp [firstMember, FullPolyMorphism.Members.comp]

/--
For inhabited full poly-morphisms, Lean composition is exactly the paper's
multiplicity-free set of pairwise composites.
-/
theorem pairwiseCompositeSet_eq_univ
    (first : InhabitedFullPolyMorphism source middle)
    (second : InhabitedFullPolyMorphism middle target) :
    FullPolyMorphism.pairwiseCompositeSet
        first.toFullPolyMorphism second.toFullPolyMorphism =
      Set.univ := by
  ext member
  constructor
  · intro _
    trivial
  · intro _
    exact first.members_comp_surjective second member

end InhabitedFullPolyMorphism

/-
The empty-intermediate regression for full-poly composition.  Isomorphic
singleton endpoints can have a non-isomorphic singleton intermediate, so
both input member sets are empty although the full endpoint member set is
inhabited.
-/
namespace EmptyIntermediateRegression

/-- A one-object capsule in the discrete category on two objects. -/
private def singletonCapsule (X : Discrete Bool) :
    CategoryCapsule (CategoryTheory.Cat.of (Discrete Bool)) where
  index := PUnit
  object _ := X

private abbrev source := singletonCapsule (Discrete.mk false)
private abbrev middle := singletonCapsule (Discrete.mk true)
private abbrev target := singletonCapsule (Discrete.mk false)

private def first : FullPolyMorphism source middle where
  indexEmbedding := Function.Embedding.refl PUnit

private def second : FullPolyMorphism middle target where
  indexEmbedding := Function.Embedding.refl PUnit

/-- The first full member set is empty because its discrete objects differ. -/
theorem first_members_empty : ¬ Nonempty first.Members := by
  rintro ⟨member⟩
  have impossible : false = true :=
    Discrete.eq_of_hom (member PUnit.unit).hom
  exact Bool.false_ne_true impossible

/-- The second full member set is likewise empty in the reverse direction. -/
theorem second_members_empty : ¬ Nonempty second.Members := by
  rintro ⟨member⟩
  have impossible : true = false :=
    Discrete.eq_of_hom (member PUnit.unit).hom
  exact Bool.false_ne_true impossible.symm

/-- The isomorphic endpoints nevertheless supply a member of the full composite. -/
private def endpointMember : (first.comp second).Members :=
  fun _ => Iso.refl (Discrete.mk false)

/-- The actual pairwise composite set is empty in the regression example. -/
theorem pairwiseCompositeSet_empty :
    first.pairwiseCompositeSet second = ∅ := by
  ext member
  constructor
  · rintro ⟨members, _⟩
    exact first_members_empty ⟨members.1⟩
  · simp

/--
Consequently, replacing pairwise composition by the entire full endpoint set
is invalid without the inhabitation condition imposed on procession arrows.
-/
theorem pairwiseCompositeSet_ne_univ :
    first.pairwiseCompositeSet second ≠ Set.univ := by
  intro set_eq
  have endpoint_mem : endpointMember ∈ first.pairwiseCompositeSet second := by
    rw [set_eq]
    trivial
  rw [pairwiseCompositeSet_empty] at endpoint_mem
  exact endpoint_mem

end EmptyIntermediateRegression

end CategoryCapsule

/--
A positive-length procession of a category, as in IUT I, Definition 4.10.

The `j`-th entry is a `(j+1)`-capsule.  The arrows drawn between adjacent
capsules in the paper are the derived types of all capsule-full
poly-morphisms, exposed below as `transition`.
-/
structure CategoryProcession
    (C : CategoryTheory.Cat.{v, u}) (length : ℕ+) where
  capsule : Fin length.1 -> CategoryCapsule C
  capsule_card :
    ∀ j, Fintype.card (capsule j).index = j.1 + 1

namespace CategoryProcession

variable {C : CategoryTheory.Cat.{v, u}}
variable {n m : ℕ+}

/-- Apply a functor to every object in a procession. -/
def map
    {D : CategoryTheory.Cat.{v, u}}
    (F : C ⥤ D)
    (P : CategoryProcession C n) :
    CategoryProcession D n where
  capsule j := CategoryCapsule.map F (P.capsule j)
  capsule_card j := P.capsule_card j

/--
The arrow at an adjacent pair in a procession: the collection of all
capsule-full poly-morphisms between the two capsules.
-/
def transition (P : CategoryProcession C n)
    (j : Fin (n.1 - 1)) :
    Type u :=
  CategoryCapsule.FullPolyMorphism
    (P.capsule ⟨j.1, lt_of_lt_of_le j.2 (Nat.sub_le _ _)⟩)
    (P.capsule ⟨j.1 + 1, by omega⟩)

/--
A morphism of processions: an order-preserving injection of positions and an
inhabited capsule-full poly-morphism at every retained position.  Inhabitation
is exactly what makes composition agree with the paper's pairwise set rule.
-/
structure Hom
    (source : CategoryProcession C n)
    (target : CategoryProcession C m) where
  positionEmbedding : Fin n.1 ↪ Fin m.1
  positionStrictMono : StrictMono positionEmbedding
  component :
    ∀ j,
      CategoryCapsule.InhabitedFullPolyMorphism
        (source.capsule j)
        (target.capsule (positionEmbedding j))

namespace Hom

variable {r : ℕ+}
variable {source : CategoryProcession C n}
variable {target : CategoryProcession C m}
variable {third : CategoryProcession C r}

/-- Apply a functor to a procession morphism. -/
def map
    {D : CategoryTheory.Cat.{v, u}}
    (F : C ⥤ D)
    (f : Hom source target) :
    Hom (CategoryProcession.map F source)
      (CategoryProcession.map F target) where
  positionEmbedding := f.positionEmbedding
  positionStrictMono := f.positionStrictMono
  component j := (f.component j).map F

@[ext]
theorem ext (f g : Hom source target)
    (positionEmbedding_eq :
      f.positionEmbedding = g.positionEmbedding)
    (component_eq : HEq f.component g.component) :
    f = g := by
  cases f with
  | mk fEmbedding fStrictMono fComponent =>
    cases g with
    | mk gEmbedding gStrictMono gComponent =>
      cases positionEmbedding_eq
      simp only [heq_eq_eq] at component_eq
      congr

/-- Identity morphism of a procession. -/
def id (source : CategoryProcession C n) :
    Hom source source where
  positionEmbedding := Function.Embedding.refl (Fin n.1)
  positionStrictMono := strictMono_id
  component j :=
    CategoryCapsule.InhabitedFullPolyMorphism.id (source.capsule j)

/-- Composition of procession morphisms. -/
def comp (f : Hom source target) (g : Hom target third) :
    Hom source third where
  positionEmbedding :=
    f.positionEmbedding.trans g.positionEmbedding
  positionStrictMono :=
    g.positionStrictMono.comp f.positionStrictMono
  component j :=
    (f.component j).comp
      (g.component (f.positionEmbedding j))

end Hom

/-- A procession morphism forces the source length to be at most the target length. -/
theorem Hom.length_le
    {source : CategoryProcession C n}
    {target : CategoryProcession C m}
    (f : Hom source target) :
    n.1 ≤ m.1 := by
  simpa using
    Fintype.card_le_of_injective
      f.positionEmbedding f.positionEmbedding.injective

end CategoryProcession

namespace CategoryCapsule

variable {C : CategoryTheory.Cat.{v, u}}
variable {n : ℕ+}

/-- A finite ordinal lifted to the universe of a capsule index type. -/
abbrev FiniteIndex (cardinality : ℕ) : Type u :=
  ULift.{u} (Fin cardinality)

/--
The procession of nested initial subcapsules determined by an ordering of a
capsule's index set.  This is the abstract construction used in IUT I,
Proposition 4.11(i).
-/
def nestedProcession
    (capsule : CategoryCapsule C)
    (indexOrder : capsule.index ≃ FiniteIndex n.1) :
    CategoryProcession C n where
  capsule j :=
    { index := FiniteIndex (j.1 + 1)
      object := fun i =>
        capsule.object
          (indexOrder.symm
            (ULift.up
              ⟨i.down.1,
                lt_of_lt_of_le i.down.2
                  (Nat.succ_le_iff.mpr j.2)⟩)) }
  capsule_card j := by
    simp [FiniteIndex]

/-- The fixed inclusion underlying the adjacent arrow of a nested procession. -/
def nestedTransition
    (capsule : CategoryCapsule C)
    (indexOrder : capsule.index ≃ FiniteIndex n.1)
    (j : Fin (n.1 - 1)) :
    (capsule.nestedProcession indexOrder).transition j where
  indexEmbedding :=
    { toFun := fun i =>
        ULift.up
          ⟨i.down.1,
            lt_trans i.down.2 (Nat.lt_succ_self _)⟩
      inj' := fun _ _ h => by
        apply ULift.ext
        apply Fin.ext
        exact congrArg (fun z => z.down.1) h }

/--
The adjacent full-poly morphism is inhabited: the canonical member uses
identity isomorphisms on the retained objects.
-/
def nestedTransitionMember
    (capsule : CategoryCapsule C)
    (indexOrder : capsule.index ≃ FiniteIndex n.1)
    (j : Fin (n.1 - 1)) :
    (capsule.nestedTransition indexOrder j).Members :=
  fun _ => Iso.refl _

/-- The product of the successive label-choice cardinalities is `n!`. -/
theorem nested_label_indeterminacy
    (capsule : CategoryCapsule C)
    (indexOrder : capsule.index ≃ FiniteIndex n.1) :
    (∏ j : Fin n.1,
      Fintype.card
        ((capsule.nestedProcession indexOrder).capsule
          j).index) =
      Nat.factorial n.1 := by
  change
    (∏ j : Fin n.1,
      Fintype.card (ULift.{u} (Fin (j.1 + 1)))) =
        Nat.factorial n.1
  simp_rw [Fintype.card_ulift, Fintype.card_fin]
  simpa only [] using
    (Fin.prod_univ_eq_prod_range
      (fun j : ℕ => j + 1) n.1).trans
        (Finset.prod_range_add_one_eq_factorial n.1)

end CategoryCapsule

/-- A procession together with its positive length. -/
structure CategoryProcessionObject
    (C : CategoryTheory.Cat.{v, u}) where
  length : ℕ+
  procession : CategoryProcession C length

namespace CategoryProcessionObject

variable {C : CategoryTheory.Cat.{v, u}}

/-- Morphisms in the category of processions allow the length to increase. -/
abbrev Hom
    (source target : CategoryProcessionObject C) :=
  CategoryProcession.Hom source.procession target.procession

instance : Category (CategoryProcessionObject C) where
  Hom := Hom
  id source := CategoryProcession.Hom.id source.procession
  comp f g := CategoryProcession.Hom.comp f g
  id_comp f := by
    apply CategoryProcession.Hom.ext
    · rfl
    · apply heq_of_eq
      funext j
      apply CategoryCapsule.InhabitedFullPolyMorphism.ext
      rfl
  comp_id f := by
    apply CategoryProcession.Hom.ext
    · rfl
    · apply heq_of_eq
      funext j
      apply CategoryCapsule.InhabitedFullPolyMorphism.ext
      rfl
  assoc f g h := by
    apply CategoryProcession.Hom.ext
    · rfl
    · apply heq_of_eq
      funext j
      apply CategoryCapsule.InhabitedFullPolyMorphism.ext
      rfl

end CategoryProcessionObject

namespace CategoryCapsule

variable {C : CategoryTheory.Cat.{v, u}}

/--
A capsule-full morphism together with one actual componentwise isomorphism
member.  The paper's poly-morphisms retain these members; the earlier
`FullPolyMorphism` records only their common index embedding.
-/
structure FullMemberMorphism (source target : CategoryCapsule C) where
  indexEmbedding : source.index ↪ target.index
  componentIso :
    ∀ index, source.object index ≅ target.object (indexEmbedding index)

namespace FullMemberMorphism

variable {source middle target : CategoryCapsule C}

@[ext]
theorem ext (first second : FullMemberMorphism source target)
    (indexEmbedding_eq : first.indexEmbedding = second.indexEmbedding)
    (componentIso_eq : HEq first.componentIso second.componentIso) :
    first = second := by
  cases first
  cases second
  cases indexEmbedding_eq
  simp only [heq_eq_eq] at componentIso_eq
  congr

/-- Forget the chosen member but retain its capsule-full poly-morphism. -/
def toFullPolyMorphism
    (morphism : FullMemberMorphism source target) :
    FullPolyMorphism source target where
  indexEmbedding := morphism.indexEmbedding

/--
Forget the chosen member while retaining the proposition that the full member
set is inhabited.  This is the procession-arrow representation.
-/
def toInhabitedFullPolyMorphism
    (morphism : FullMemberMorphism source target) :
    InhabitedFullPolyMorphism source target where
  toFullPolyMorphism := morphism.toFullPolyMorphism
  members_nonempty := ⟨morphism.componentIso⟩

/-- The chosen isomorphisms form a member of the forgotten poly-morphism. -/
def member (morphism : FullMemberMorphism source target) :
    morphism.toFullPolyMorphism.Members :=
  morphism.componentIso

def id (source : CategoryCapsule C) : FullMemberMorphism source source where
  indexEmbedding := Function.Embedding.refl source.index
  componentIso index := Iso.refl (source.object index)

def comp (first : FullMemberMorphism source middle)
    (second : FullMemberMorphism middle target) :
    FullMemberMorphism source target where
  indexEmbedding := first.indexEmbedding.trans second.indexEmbedding
  componentIso index :=
    (first.componentIso index).trans
      (second.componentIso (first.indexEmbedding index))

/-- A capsule endomorphism's finite index embedding as an equivalence. -/
noncomputable def indexEquivSelf
    (morphism : FullMemberMorphism source source) :
    source.index ≃ source.index :=
  Equiv.ofBijective morphism.indexEmbedding
    ⟨morphism.indexEmbedding.injective,
      Finite.surjective_of_injective morphism.indexEmbedding.injective⟩

@[simp]
theorem indexEquivSelf_apply
    (morphism : FullMemberMorphism source source)
    (index : source.index) :
    morphism.indexEquivSelf index = morphism.indexEmbedding index :=
  rfl

@[simp]
theorem indexEquivSelf_id :
    (id source).indexEquivSelf = Equiv.refl source.index := by
  ext index
  rfl

theorem indexEquivSelf_comp
    (first second : FullMemberMorphism source source) :
    (first.comp second).indexEquivSelf =
      first.indexEquivSelf.trans second.indexEquivSelf := by
  ext index
  rfl

end FullMemberMorphism

end CategoryCapsule

namespace CategoryProcession

variable {C : CategoryTheory.Cat.{v, u}}
variable {n m r : ℕ+}

/-- A procession morphism carrying an actual member at every capsule position. -/
structure MemberHom
    (source : CategoryProcession C n)
    (target : CategoryProcession C m) where
  positionEmbedding : Fin n.1 ↪ Fin m.1
  positionStrictMono : StrictMono positionEmbedding
  component :
    ∀ position,
      CategoryCapsule.FullMemberMorphism
        (source.capsule position)
        (target.capsule (positionEmbedding position))

namespace MemberHom

variable {source : CategoryProcession C n}
variable {middle : CategoryProcession C m}
variable {target : CategoryProcession C r}

@[ext]
theorem ext (first second : MemberHom source middle)
    (positionEmbedding_eq :
      first.positionEmbedding = second.positionEmbedding)
    (component_eq : HEq first.component second.component) :
    first = second := by
  cases first
  cases second
  cases positionEmbedding_eq
  simp only [heq_eq_eq] at component_eq
  congr

/-- Forget actual members and recover the earlier procession poly-morphism. -/
def toHom (morphism : MemberHom source middle) : Hom source middle where
  positionEmbedding := morphism.positionEmbedding
  positionStrictMono := morphism.positionStrictMono
  component position :=
    (morphism.component position).toInhabitedFullPolyMorphism

def id (source : CategoryProcession C n) : MemberHom source source where
  positionEmbedding := Function.Embedding.refl (Fin n.1)
  positionStrictMono := strictMono_id
  component position :=
    CategoryCapsule.FullMemberMorphism.id (source.capsule position)

def comp (first : MemberHom source middle)
    (second : MemberHom middle target) : MemberHom source target where
  positionEmbedding :=
    first.positionEmbedding.trans second.positionEmbedding
  positionStrictMono :=
    second.positionStrictMono.comp first.positionStrictMono
  component position :=
    (first.component position).comp
      (second.component (first.positionEmbedding position))

/-- An endomorphism of a finite procession fixes every capsule position. -/
@[simp]
theorem positionEmbedding_apply_self
    (morphism : MemberHom source source) (position : Fin n.1) :
    morphism.positionEmbedding position = position := by
  exact le_antisymm
    morphism.positionStrictMono.apply_le
    morphism.positionStrictMono.le_apply

/-- The position embedding of a procession endomorphism is the identity. -/
theorem positionEmbedding_self
    (morphism : MemberHom source source) :
    morphism.positionEmbedding = Function.Embedding.refl (Fin n.1) := by
  ext position
  exact congrArg Fin.val (morphism.positionEmbedding_apply_self position)

/-- Recast a component member at an explicitly equal target position. -/
noncomputable def componentAtTarget
    (morphism : MemberHom source source)
    (sourcePosition targetPosition : Fin n.1)
    (compatible : morphism.positionEmbedding sourcePosition = targetPosition) :
    CategoryCapsule.FullMemberMorphism
      (source.capsule sourcePosition) (source.capsule targetPosition) := by
  subst targetPosition
  exact morphism.component sourcePosition

/-- Explicit target-position recasting preserves composition. -/
theorem componentAtTarget_comp
    (first second : MemberHom source source)
    (sourcePosition middlePosition targetPosition : Fin n.1)
    (firstCompatible :
      first.positionEmbedding sourcePosition = middlePosition)
    (secondCompatible :
      second.positionEmbedding middlePosition = targetPosition)
    (combinedCompatible :
      (first.comp second).positionEmbedding sourcePosition = targetPosition) :
    (first.comp second).componentAtTarget sourcePosition targetPosition
        combinedCompatible =
      (first.componentAtTarget sourcePosition middlePosition firstCompatible).comp
        (second.componentAtTarget middlePosition targetPosition
          secondCompatible) := by
  subst middlePosition
  subst targetPosition
  rfl

/-- The actual capsule member of an endomorphism at its fixed position. -/
noncomputable def componentSelf
    (morphism : MemberHom source source) (position : Fin n.1) :
    CategoryCapsule.FullMemberMorphism
      (source.capsule position) (source.capsule position) :=
  morphism.componentAtTarget position position
    (morphism.positionEmbedding_apply_self position)

@[simp]
theorem componentSelf_id (position : Fin n.1) :
    (id source).componentSelf position =
      CategoryCapsule.FullMemberMorphism.id (source.capsule position) := by
  apply CategoryCapsule.FullMemberMorphism.ext
  · apply Function.Embedding.ext
    intro index
    rfl
  · apply heq_of_eq
    funext index
    apply Iso.ext
    rfl

theorem componentSelf_comp
    (first second : MemberHom source source) (position : Fin n.1) :
    (first.comp second).componentSelf position =
      (first.componentSelf position).comp
        (second.componentSelf position) := by
  exact componentAtTarget_comp first second position position position
    (first.positionEmbedding_apply_self position)
    (second.positionEmbedding_apply_self position)
    ((first.comp second).positionEmbedding_apply_self position)

end MemberHom

end CategoryProcession

/-- A procession object in the category whose arrows retain actual members. -/
structure CategoryProcessionMemberObject
    (C : CategoryTheory.Cat.{v, u}) where
  length : ℕ+
  procession : CategoryProcession C length

namespace CategoryProcessionMemberObject

variable {C : CategoryTheory.Cat.{v, u}}

abbrev Hom (source target : CategoryProcessionMemberObject C) :=
  CategoryProcession.MemberHom source.procession target.procession

instance : Category (CategoryProcessionMemberObject C) where
  Hom := Hom
  id source := CategoryProcession.MemberHom.id source.procession
  comp first second := CategoryProcession.MemberHom.comp first second
  id_comp morphism := by
    apply CategoryProcession.MemberHom.ext
    · rfl
    · apply heq_of_eq
      funext position
      apply CategoryCapsule.FullMemberMorphism.ext
      · rfl
      · apply heq_of_eq
        funext index
        apply Iso.ext
        simp [CategoryProcession.MemberHom.comp,
          CategoryProcession.MemberHom.id,
          CategoryCapsule.FullMemberMorphism.comp,
          CategoryCapsule.FullMemberMorphism.id]
  comp_id morphism := by
    apply CategoryProcession.MemberHom.ext
    · rfl
    · apply heq_of_eq
      funext position
      apply CategoryCapsule.FullMemberMorphism.ext
      · rfl
      · apply heq_of_eq
        funext index
        apply Iso.ext
        simp [CategoryProcession.MemberHom.comp,
          CategoryProcession.MemberHom.id,
          CategoryCapsule.FullMemberMorphism.comp,
          CategoryCapsule.FullMemberMorphism.id]
  assoc first second third := by
    apply CategoryProcession.MemberHom.ext
    · rfl
    · apply heq_of_eq
      funext position
      apply CategoryCapsule.FullMemberMorphism.ext
      · rfl
      · apply heq_of_eq
        funext index
        apply Iso.ext
        simp [CategoryProcession.MemberHom.comp,
          CategoryCapsule.FullMemberMorphism.comp]

end CategoryProcessionMemberObject

end Iut
