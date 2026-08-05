/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Topology.Algebra.Monoid.Defs

namespace Iut

universe u

structure TopologicalMonoidPresentation where
  carrier : Type u
  [monoid : Monoid carrier]
  [topology : TopologicalSpace carrier]
  [continuousMul : ContinuousMul carrier]

attribute [instance] TopologicalMonoidPresentation.monoid
attribute [instance] TopologicalMonoidPresentation.topology
attribute [instance] TopologicalMonoidPresentation.continuousMul

structure ContinuousMonoidHom
    (M N : TopologicalMonoidPresentation.{u}) where
  hom : M.carrier →* N.carrier
  continuous : Continuous hom

namespace ContinuousMonoidHom

instance {M N : TopologicalMonoidPresentation.{u}} :
    CoeFun (ContinuousMonoidHom M N) (fun _ => M.carrier → N.carrier) :=
  ⟨fun f => f.hom⟩

def comp {M N P : TopologicalMonoidPresentation.{u}}
    (f : ContinuousMonoidHom M N)
    (g : ContinuousMonoidHom N P) :
    ContinuousMonoidHom M P where
  hom := g.hom.comp f.hom
  continuous := g.continuous.comp f.continuous

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

end ContinuousMonoidHom

end Iut
