/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceConnectedAnabelioidSlice
import Mathlib.CategoryTheory.Galois.Equivalence
import Mathlib.CategoryTheory.Limits.IsConnected

/-!
# Connected covering categories

For a profinite group `G`, the category `B(G)⁰` in the IUT papers is the full
subcategory of finite continuous `G`-actions that are connected as objects of
the Galois category `B(G)`.  This file constructs that category from `G`; it
does not take a category or its categorical laws as additional input.

The two structural facts needed by the Frobenioid base-category interface are
proved here: `B(G)⁰` is a connected category, and every one of its morphisms is
an epimorphism.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

/-- The Galois-theoretic connected-object property on finite continuous
`G`-actions. -/
abbrev sourceConnectedContinuousAction (G : ProfiniteGrp.{u}) :
    ObjectProperty (ContAction FintypeCat.{u} G) :=
  fun X => PreGaloisCategory.IsConnected X

/-- `B(G)⁰`: connected finite continuous `G`-actions and all equivariant maps
between them. -/
abbrev SourceConnectedCoveringCategory (G : ProfiniteGrp.{u}) :=
  (sourceConnectedContinuousAction G).FullSubcategory

namespace SourceConnectedCoveringCategory

variable (G : ProfiniteGrp.{u})

/-- The source object of `B(G)⁰` retains its actual finite continuous action. -/
abbrev action (X : SourceConnectedCoveringCategory G) :
    ContAction FintypeCat.{u} G :=
  X.obj

/-- The stored object condition is available to the Galois-category API. -/
instance connectedObject (X : SourceConnectedCoveringCategory G) :
    PreGaloisCategory.IsConnected X.obj :=
  X.property

/-- Every connected finite continuous action has a nonempty fiber. -/
instance nonemptyFiber (X : SourceConnectedCoveringCategory G) :
    Nonempty X.obj.obj.V := by
  change Nonempty ((continuousActionFiber G).obj X.obj)
  infer_instance

/-- Every arrow between connected covers is an epimorphism. -/
instance epi (X Y : SourceConnectedCoveringCategory G) (f : X ⟶ Y) : Epi f := by
  apply (sourceConnectedContinuousAction G).ι.epi_of_epi_map
  exact epi_of_nonempty_of_isConnected (continuousActionFiber G) f.hom

/-- The terminal continuous action, regarded as a connected cover. -/
noncomputable def terminalObject : SourceConnectedCoveringCategory G := by
  let terminalAction : ContAction FintypeCat.{u} G := ⊤_ _
  refine ⟨terminalAction, ?_⟩
  exact sourceGaloisCategory_isConnected_of_isTerminal
    terminalAction terminalIsTerminal

/-- The lifted terminal object is terminal in `B(G)⁰`. -/
noncomputable def terminalObjectIsTerminal : IsTerminal (terminalObject G) where
  lift X := ObjectProperty.homMk (terminal.from X.pt.obj)
  fac X j := isEmptyElim j.as
  uniq X f _ := by
    apply ObjectProperty.hom_ext
    exact terminal.hom_ext f.hom (terminal.from X.pt.obj)

/-- `B(G)⁰` is connected: every connected cover maps to its terminal connected
cover. -/
noncomputable instance categoryIsConnected :
    CategoryTheory.IsConnected (SourceConnectedCoveringCategory G) :=
  CategoryTheory.isConnected_of_isTerminal _ (terminalObjectIsTerminal G)

/-- Connectedness of a continuous action is equivalent to transitivity of the
underlying nonempty finite action. -/
theorem connected_iff_pretransitive
    (X : ContAction FintypeCat.{u} G) [Nonempty X.obj.V] :
    PreGaloisCategory.IsConnected X ↔
      MulAction.IsPretransitive G X.obj.V := by
  constructor
  · intro connected
    letI : PreGaloisCategory.IsConnected X := connected
    exact continuousAction_pretransitive_of_isConnected G X
  · intro transitive
    letI : MulAction.IsPretransitive G X.obj.V := transitive
    refine
      { notInitial := ?_
        noTrivialComponent := ?_ }
    · exact not_initial_of_inhabited (continuousActionFiber G)
        (Classical.arbitrary X.obj.V)
    · intro Y inclusion _ noninitial
      have fiberSourceNonempty : Nonempty Y.obj.V := by
        change Nonempty ((continuousActionFiber G).obj Y)
        exact (not_initial_iff_fiber_nonempty
          (continuousActionFiber G) Y).mp noninitial
      haveI : Mono ((continuousActionFiber G).map inclusion) := inferInstance
      have fiberMapInjective :
          Function.Injective ((continuousActionFiber G).map inclusion) :=
        (ConcreteCategory.mono_iff_injective_of_preservesPullback
          ((continuousActionFiber G).map inclusion)).mp inferInstance
      have fiberMapSurjective :
          Function.Surjective ((continuousActionFiber G).map inclusion) := by
        intro target
        obtain ⟨source⟩ := fiberSourceNonempty
        obtain ⟨g, hg⟩ := transitive.exists_smul_eq
          (((continuousActionFiber G).map inclusion) source) target
        refine ⟨g • source, ?_⟩
        change (Y.obj.ρ g ≫ inclusion.hom.hom) source = target
        rw [inclusion.hom.comm g, FintypeCat.comp_apply]
        exact hg
      haveI : IsIso ((continuousActionFiber G).map inclusion) :=
        (ConcreteCategory.isIso_iff_bijective _).mpr
          ⟨fiberMapInjective, fiberMapSurjective⟩
      exact isIso_of_reflects_iso inclusion (continuousActionFiber G)

end SourceConnectedCoveringCategory

namespace EtaleFundamentalGroup

/-- A certified finite-etale covering category is equivalent to finite
continuous actions of its stored profinite fundamental group.  The first
equivalence is the Galois-category reconstruction; the second transports the
action from automorphisms of the fiber functor across the stored fundamental
group certificate. -/
noncomputable def coverActionEquivalence
    (data : EtaleFundamentalGroup.{u}) :
    letI := data.coverCategory
    data.Cover ≌ ContAction FintypeCat.{u} data.group := by
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  exact
    (PreGaloisCategory.functorToContAction data.fiber).asEquivalence.trans
      (ContAction.resEquiv FintypeCat
        (SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv data))

end EtaleFundamentalGroup

end Iut
