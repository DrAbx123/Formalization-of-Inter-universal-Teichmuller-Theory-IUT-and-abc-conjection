/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
/-!
Foundational bookkeeping for the IUT formalization.

This file starts with a deliberately small interface for species, mutations, and
labeled copies. It is not yet a formalization of Mochizuki's set-theoretic
species/mutation formalism; it is a typed scaffold for the first Stage 1 models.
-/

namespace Iut

universe u v

/-- A provisional species is a type of objects. Morphisms and formulas will be
added only when a concrete formalization step needs them. -/
structure Species where
  Obj : Type u

/-- A provisional mutation maps objects of one species to objects of another. -/
structure Mutation (source : Species.{u}) (target : Species.{v}) where
  mapObj : source.Obj -> target.Obj

/-- A copy of an object with an explicit label. The label is part of the data. -/
structure LabeledCopy (alpha : Type u) where
  label : String
  carrier : alpha
deriving Repr

namespace LabeledCopy

variable {alpha : Type u}

/-- Forget the label attached to a copy. This operation is intentionally explicit. -/
def forget (x : LabeledCopy alpha) : alpha :=
  x.carrier

@[simp]
theorem forget_mk (label : String) (carrier : alpha) :
    forget ({ label := label, carrier := carrier } : LabeledCopy alpha) = carrier :=
  rfl

/-- Two labeled copies are label-compatible when their labels agree. -/
def LabelCompatible (x y : LabeledCopy alpha) : Prop :=
  x.label = y.label

/-- Two labeled copies have the same underlying carrier after labels are forgotten. -/
def SameCarrier (x y : LabeledCopy alpha) : Prop :=
  x.forget = y.forget

end LabeledCopy

/-- A named indeterminacy, together with the bookkeeping needed in early models. -/
structure Indeterminacy where
  name : String
  actsOnLogShells : Bool
  absorbedByHull : Bool
deriving Repr

/-- A finite list of indeterminacies carried by a construction. -/
abbrev IndeterminacyProfile :=
  List Indeterminacy

end Iut
