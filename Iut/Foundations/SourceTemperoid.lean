/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceConnectedCoveringCategory
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Limits.IsConnected

/-!
# Countable temperoids

For a topological group `G`, the source category `B^temp(G)` is the category
of countable discrete sets equipped with a continuous `G`-action.  Its
connected objects are precisely the nonempty transitive actions.  This file
constructs the category directly from `G`, proves the connected-category and
epimorphism properties used in the source, and embeds the finite continuous
actions as its finite subcategory.

The construction follows Semi-graphs of Anabelioids, Definition 3.1 and
Remarks 3.1.1--3.1.5, and IUT I, Example 3.2(i).
-/

namespace Iut

universe u v

open CategoryTheory
open CategoryTheory.Limits

/-- The category of countable types and all functions between them. -/
abbrev SourceCountableTypeCat :=
  ObjectProperty.FullSubcategory (C := Type*) Countable

namespace SourceCountableTypeCat

/-- Bundle a type with its countability certificate. -/
abbrev of (X : Type u) [Countable X] : SourceCountableTypeCat.{u} :=
  ⟨X, inferInstance⟩

instance : CoeSort SourceCountableTypeCat.{u} (Type u) :=
  ⟨fun X => X.obj⟩

instance (X : SourceCountableTypeCat.{u}) : Countable X :=
  X.property

/-- Construct a morphism of countable types from a function. -/
def homMk {X Y : SourceCountableTypeCat.{u}} (f : X → Y) : X ⟶ Y where
  hom := ↾f

@[simp]
theorem homMk_apply {X Y : SourceCountableTypeCat.{u}}
    (f : X → Y) (x : X) :
    homMk f x = f x :=
  rfl

@[simp]
theorem comp_apply {X Y Z : SourceCountableTypeCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) :=
  rfl

/-- Bundle a multiplicative action on a countable type. -/
def ofMulAction (G : Type*) (H : SourceCountableTypeCat.{u})
    [Monoid G] [MulAction G H] :
    Action SourceCountableTypeCat.{u} G where
  V := H
  ρ :=
    InducedCategory.endEquiv.symm.toMonoidHom.comp
      ((TypeCat.endEquiv _).toMonoidHom.comp MulAction.toEndHom)

@[simp]
theorem ofMulAction_apply {G : Type*} {H : SourceCountableTypeCat.{u}}
    [Monoid G] [MulAction G H] (g : G) (x : H) :
    ConcreteCategory.hom ((ofMulAction G H).ρ g) x = g • x :=
  rfl

end SourceCountableTypeCat

namespace SourceCountableTypeCatDiscrete

/-- Countable carriers in a temperoid have the discrete topology. -/
scoped instance (X : SourceCountableTypeCat.{u}) : TopologicalSpace X := ⊥

scoped instance (X : SourceCountableTypeCat.{u}) : DiscreteTopology X :=
  ⟨rfl⟩

/-- Regard a countable discrete type as a topological space. -/
scoped instance : HasForget₂ SourceCountableTypeCat.{u} TopCat.{u} where
  forget₂.obj X := TopCat.of X
  forget₂.map f := TopCat.ofHom ⟨f, continuous_of_discreteTopology⟩

end SourceCountableTypeCatDiscrete

open scoped FintypeCatDiscrete SourceCountableTypeCatDiscrete

/-- `B^temp(G)`: countable discrete sets with continuous `G`-action. -/
abbrev SourceTemperoidAction (G : Type v) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :=
  ContAction SourceCountableTypeCat.{u} G

namespace SourceTemperoidAction

/-- The action stored by a temperoid object, exposed on its concrete carrier. -/
instance carrierMulAction (G : Type v) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (X : SourceTemperoidAction.{u, v} G) :
    MulAction G X.obj.V.obj where
  smul g x := ConcreteCategory.hom (X.obj.ρ g) x
  one_smul x := by
    change ConcreteCategory.hom (X.obj.ρ 1) x = x
    rw [map_one]
    rfl
  mul_smul g h x := by
    change ConcreteCategory.hom (X.obj.ρ (g * h)) x =
      ConcreteCategory.hom (X.obj.ρ g)
        (ConcreteCategory.hom (X.obj.ρ h) x)
    rw [map_mul]
    rfl

/-- Continuity stored by a temperoid object, exposed on its concrete carrier. -/
instance carrierContinuousSMul (G : Type v) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (X : SourceTemperoidAction.{u, v} G) :
    ContinuousSMul G X.obj.V.obj := by
  change ContinuousSMul G
    ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).obj X.obj)
  exact X.property

end SourceTemperoidAction

/-- The connected-object property in a temperoid: nonempty and transitive. -/
abbrev sourceConnectedTemperoidAction
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ObjectProperty (SourceTemperoidAction.{u, v} G) :=
  fun X =>
    Nonempty
        ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).obj X.obj) ∧
      MulAction.IsPretransitive G
        ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).obj X.obj)

/-- The connected temperoid `B^temp(G)⁰`. -/
abbrev SourceConnectedTemperoid
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :=
  (sourceConnectedTemperoidAction.{u, v} G).FullSubcategory

namespace SourceConnectedTemperoid

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- For a countable continuous action, membership in the connected temperoid
is exactly nonemptiness together with transitivity. -/
theorem connected_iff_nonempty_pretransitive
    (X : SourceTemperoidAction.{u, v} G) :
    sourceConnectedTemperoidAction.{u, v} G X ↔
      (Nonempty
          ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).obj X.obj) ∧
        MulAction.IsPretransitive G
          ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).obj X.obj)) :=
  Iff.rfl

/-- The carrier of a connected temperoid object is nonempty. -/
instance nonemptyFiber (X : SourceConnectedTemperoid.{u, v} G) :
    Nonempty ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).obj X.obj.obj) :=
  X.property.1

/-- The action on a connected temperoid object is transitive. -/
instance pretransitive (X : SourceConnectedTemperoid.{u, v} G) :
    MulAction.IsPretransitive G
      ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).obj X.obj.obj) :=
  X.property.2

/-- An equivariant map between nonempty transitive actions is surjective. -/
theorem hom_surjective
    (X Y : SourceConnectedTemperoid.{u, v} G) (f : X ⟶ Y) :
    Function.Surjective
      ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).map f.hom.hom) := by
  intro y
  obtain ⟨x⟩ := nonemptyFiber G X
  obtain ⟨g, hg⟩ := (pretransitive G Y).exists_smul_eq
    ((forget₂ (Action SourceCountableTypeCat.{u} G) TopCat).map f.hom.hom x) y
  refine ⟨g • x, ?_⟩
  exact (ConcreteCategory.congr_hom (f.hom.hom.comm g) x).trans hg

/-- Every arrow between connected temperoid objects is an epimorphism. -/
instance epi (X Y : SourceConnectedTemperoid.{u, v} G) (f : X ⟶ Y) : Epi f := by
  apply (sourceConnectedTemperoidAction.{u, v} G).ι.epi_of_epi_map
  apply ConcreteCategory.epi_of_surjective
  exact hom_surjective G X Y f

/-- The one-point trivial continuous action. -/
noncomputable def terminalAction : SourceTemperoidAction.{u, v} G := by
  refine ⟨Action.trivial G (SourceCountableTypeCat.of PUnit), ?_⟩
  change ContinuousSMul G PUnit
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  convert isOpen_univ
  ext g
  simp [MulAction.mem_stabilizer_iff]

/-- The one-point action is connected. -/
noncomputable def terminalObject : SourceConnectedTemperoid.{u, v} G := by
  refine ⟨terminalAction G, ?_⟩
  dsimp [sourceConnectedTemperoidAction, terminalAction]
  constructor
  · exact ⟨PUnit.unit⟩
  · constructor
    intro first second
    cases first
    cases second
    exact ⟨1, rfl⟩

/-- The one-point connected action is terminal. -/
noncomputable def terminalObjectIsTerminal : IsTerminal (terminalObject G) where
  lift X := by
    dsimp [terminalObject, terminalAction]
    exact ObjectProperty.homMk <| ObjectProperty.homMk
      { hom := SourceCountableTypeCat.homMk (fun _ => PUnit.unit)
        comm := fun g => by
          ext x
          rfl }
  fac X j := isEmptyElim j.as
  uniq X f _ := by
    dsimp [terminalObject, terminalAction] at f ⊢
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext x
    exact PUnit.ext _ _

/-- The connected temperoid is connected as a category. -/
noncomputable instance categoryIsConnected :
    CategoryTheory.IsConnected (SourceConnectedTemperoid.{u, v} G) :=
  CategoryTheory.isConnected_of_isTerminal _ (terminalObjectIsTerminal G)

end SourceConnectedTemperoid

namespace SourceTemperoidAction

/-- The inclusion of finite types into countable types. -/
def finiteCarrierInclusion : FintypeCat.{u} ⥤ SourceCountableTypeCat.{u} where
  obj X := ⟨X.obj, inferInstance⟩
  map f := SourceCountableTypeCat.homMk f
  map_id _ := rfl
  map_comp _ _ := rfl

instance finiteCarrierInclusionFull : finiteCarrierInclusion.{u}.Full where
  map_surjective f := ⟨FintypeCat.homMk f, rfl⟩

instance finiteCarrierInclusionFaithful : finiteCarrierInclusion.{u}.Faithful where
  map_injective equality := by
    apply ConcreteCategory.hom_ext
    intro x
    exact ConcreteCategory.congr_hom equality x

/-- Finite continuous actions form a full subcategory of the countable
temperoid action category. -/
noncomputable def finiteInclusion
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ContAction FintypeCat.{u} G ⥤ SourceTemperoidAction.{u, v} G :=
  (finiteCarrierInclusion.{u}).mapContAction G (fun X => by
    change ContinuousSMul G X.obj.V
    exact X.property)

instance finiteInclusionFull
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (finiteInclusion.{u, v} G).Full where
  map_surjective {X Y} f := by
    let lifted : X ⟶ Y := ObjectProperty.homMk
      ({ hom := FintypeCat.homMk f.hom.hom
         comm := fun g => by
           apply ConcreteCategory.hom_ext
           intro x
           exact ConcreteCategory.congr_hom (f.hom.comm g) x } :
        X.obj ⟶ Y.obj)
    refine ⟨lifted, ?_⟩
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    rfl

instance finiteInclusionFaithful
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (finiteInclusion.{u, v} G).Faithful where
  map_injective {X Y} {f g} equality := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    apply ConcreteCategory.hom_ext
    intro x
    have mapped := congrArg (fun h => h.hom.hom.hom x) equality
    exact mapped

/-- The finite-action inclusion is fully faithful. -/
noncomputable def finiteInclusionFullyFaithful
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (finiteInclusion.{u, v} G).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful (finiteInclusion.{u, v} G)

end SourceTemperoidAction

end Iut
