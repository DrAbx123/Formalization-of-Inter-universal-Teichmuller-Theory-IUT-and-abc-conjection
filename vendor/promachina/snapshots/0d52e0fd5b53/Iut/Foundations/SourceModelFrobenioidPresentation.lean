/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidAxioms

/-!
# Packaged source model Frobenioid

This module combines the connected and totally epimorphic model presentation
with the complete Definition 1.3 axiom value, yielding the formal
`FrobenioidPresentation` endpoint of Frobenioids I, Theorem 5.2(ii).
-/

open CategoryTheory
namespace Iut.SourceModelFrobenioid.Carrier
universe u
noncomputable section
variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

/-- Frobenioids I, Theorem 5.2(ii), packaged through Definition 1.3. -/
def frobenioidPresentation [IsConnected D]
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f) :
    FrobenioidPresentation where
  toPreFrobenioidPresentation :=
    preFrobenioidPresentation Phi data baseTotallyEpimorphic
  axioms := frobenioidAxioms baseTotallyEpimorphic

end
end Iut.SourceModelFrobenioid.Carrier
