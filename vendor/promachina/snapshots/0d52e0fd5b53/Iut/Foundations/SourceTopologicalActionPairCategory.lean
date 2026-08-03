/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceThetaEvaluation

/-!
# Equivariant morphisms of topological action pairs

This module equips the topological group/monoid action pairs used throughout
IUT II with the categorical morphisms needed by the localization diagrams of
Corollary 4.8(iii).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceTopologicalGroupMonoidActionPair

/-- An equivariant continuous morphism of topological action pairs. -/
structure Hom
    (source target : SourceTopologicalGroupMonoidActionPair.{u}) where
  groupHom : source.actingGroup ⟶ target.actingGroup
  monoidHom : source.monoidCarrier →ₜ* target.monoidCarrier
  equivariant :
    ∀ groupElement monoidElement,
      monoidHom (source.action groupElement monoidElement) =
        target.action
          (groupHom.toMonoidHom groupElement) (monoidHom monoidElement)

namespace Hom

variable
  {first second third fourth :
    SourceTopologicalGroupMonoidActionPair.{u}}

/-- Identity equivariant morphism. -/
def id (pair : SourceTopologicalGroupMonoidActionPair.{u}) : Hom pair pair where
  groupHom := 𝟙 pair.actingGroup
  monoidHom := _root_.ContinuousMonoidHom.id pair.monoidCarrier
  equivariant _ _ := rfl

/-- Composition of equivariant morphisms. -/
def comp (firstHom : Hom first second) (secondHom : Hom second third) :
    Hom first third where
  groupHom := firstHom.groupHom ≫ secondHom.groupHom
  monoidHom := secondHom.monoidHom.comp firstHom.monoidHom
  equivariant groupElement monoidElement := by
    change
      secondHom.monoidHom
          (firstHom.monoidHom
            (first.action groupElement monoidElement)) =
        third.action
          (secondHom.groupHom.toMonoidHom
            (firstHom.groupHom.toMonoidHom groupElement))
          (secondHom.monoidHom (firstHom.monoidHom monoidElement))
    rw [firstHom.equivariant, secondHom.equivariant]

@[ext]
theorem ext
    (firstHom secondHom : Hom first second)
    (groupHom_eq : firstHom.groupHom = secondHom.groupHom)
    (monoidHom_eq : firstHom.monoidHom = secondHom.monoidHom) :
    firstHom = secondHom := by
  cases firstHom
  cases secondHom
  cases groupHom_eq
  cases monoidHom_eq
  rfl

theorem id_comp (map : Hom first second) : (id first).comp map = map := by
  apply ext
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl

theorem comp_id (map : Hom first second) : map.comp (id second) = map := by
  apply ext
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl

theorem comp_assoc
    (firstHom : Hom first second)
    (secondHom : Hom second third)
    (thirdHom : Hom third fourth) :
    (firstHom.comp secondHom).comp thirdHom =
      firstHom.comp (secondHom.comp thirdHom) := by
  apply ext
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl

end Hom

instance : Category SourceTopologicalGroupMonoidActionPair where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

namespace Iso

variable
  {first second third : SourceTopologicalGroupMonoidActionPair.{u}}

/-- The forward equivariant morphism of an action-pair isomorphism. -/
def hom (pairIso : Iso first second) : first ⟶ second where
  groupHom :=
    { toMonoidHom := pairIso.groupIso.toMulEquiv.toMonoidHom
      continuous_toFun := pairIso.groupIso.continuous_toFun }
  monoidHom :=
    { toMonoidHom := pairIso.monoidIso.toMulEquiv.toMonoidHom
      continuous_toFun := pairIso.monoidIso.continuous_toFun }
  equivariant := pairIso.equivariant

@[simp]
theorem refl_hom (pair : SourceTopologicalGroupMonoidActionPair.{u}) :
    (refl pair).hom = 𝟙 pair := by
  apply Hom.ext
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl

@[simp]
theorem trans_hom
    (firstIso : Iso first second)
    (secondIso : Iso second third) :
    (firstIso.trans secondIso).hom = firstIso.hom ≫ secondIso.hom := by
  apply Hom.ext
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl

/-- An action-pair isomorphism as an isomorphism in the action-pair category. -/
def toCategoryIso (pairIso : Iso first second) : first ≅ second where
  hom := pairIso.hom
  inv := pairIso.symm.hom
  hom_inv_id := by
    apply Hom.ext
    · apply _root_.ContinuousMonoidHom.ext
      intro value
      change pairIso.groupIso.symm (pairIso.groupIso value) = value
      exact pairIso.groupIso.symm_apply_apply value
    · apply _root_.ContinuousMonoidHom.ext
      intro value
      change pairIso.monoidIso.symm (pairIso.monoidIso value) = value
      exact pairIso.monoidIso.symm_apply_apply value
  inv_hom_id := by
    apply Hom.ext
    · apply _root_.ContinuousMonoidHom.ext
      intro value
      change pairIso.groupIso (pairIso.groupIso.symm value) = value
      exact pairIso.groupIso.apply_symm_apply value
    · apply _root_.ContinuousMonoidHom.ext
      intro value
      change pairIso.monoidIso (pairIso.monoidIso.symm value) = value
      exact pairIso.monoidIso.apply_symm_apply value

end Iso

end SourceTopologicalGroupMonoidActionPair

end Iut
