/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidPresentation

open CategoryTheory

/-!
# Rational-monoid transport in the model Frobenioid

This file constructs the model instance of the contravariant transport on
`O^triangle` and the isotropic-hull injection in Frobenioids I, Proposition
2.2(ii), (iv).  The construction uses the explicit divisor and rational-
function pullbacks of Theorem 5.2's model category.
-/

namespace Iut.SourceModelFrobenioid.Carrier

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

/-- Pull a base-identity linear endomorphism along a model linear arrow. -/
def linearEndomorphismPullback
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (linear : (preFrobenioid Phi data).IsLinear arrow)
    (alpha : (preFrobenioid Phi data).LinearBaseIdentityEndomorphism target) :
    (preFrobenioid Phi data).LinearBaseIdentityEndomorphism source where
  hom :=
    { frobeniusDegree := 1
      base := 𝟙 (Object.base source)
      divisor := Phi.pullback arrow.base alpha.hom.divisor
      rationalFunction := data.rationalFunctions.pullback arrow.base
        alpha.hom.rationalFunction
      balance := by
        have pulled := congrArg (gpPullback Phi arrow.base)
          (endomorphism_divisor_eq Phi data alpha)
        change (1 : ℕ) • source.divisorClass +
              Algebra.GrothendieckAddGroup.of
                (Phi.pullback arrow.base alpha.hom.divisor) =
            gpPullback Phi (𝟙 (Object.base source)) source.divisorClass +
              data.divisor (Object.base source)
                (data.rationalFunctions.pullback arrow.base
                  alpha.hom.rationalFunction)
        rw [one_nsmul, gpPullback_id]
        simp only [AddMonoidHom.id_apply]
        rw [gpPullback_of, ← data.divisor_natural] at pulled
        rw [pulled] }
  linear := linear.symm.trans linear
  baseIdentity := rfl

theorem linearEndomorphismPullback_one
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (linear : (preFrobenioid Phi data).IsLinear arrow) :
    linearEndomorphismPullback arrow linear 1 = 1 := by
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  apply Hom.ext
  · rfl
  · rfl
  · change Phi.pullback arrow.base 0 = 0
    exact map_zero _
  · change data.rationalFunctions.pullback arrow.base 0 = 0
    exact map_zero _

theorem linearEndomorphismPullback_mul
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (linear : (preFrobenioid Phi data).IsLinear arrow)
    (left right :
      (preFrobenioid Phi data).LinearBaseIdentityEndomorphism target) :
    linearEndomorphismPullback arrow linear (left * right) =
      linearEndomorphismPullback arrow linear left *
        linearEndomorphismPullback arrow linear right := by
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  apply Hom.ext
  · change (1 : ℕ+) = 1 * 1
    rfl
  · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp
  · change Phi.pullback arrow.base
          (Phi.pullback left.hom.base right.hom.divisor +
            right.hom.frobeniusDegree.val • left.hom.divisor) =
        Phi.pullback (𝟙 (Object.base source))
            (Phi.pullback arrow.base right.hom.divisor) +
          (1 : ℕ+).val • Phi.pullback arrow.base left.hom.divisor
    have leftBase := left.baseIdentity
    change left.hom.base = 𝟙 (Object.base target) at leftBase
    have rightLinear := right.linear
    change right.hom.frobeniusDegree = 1 at rightLinear
    rw [leftBase, rightLinear, Phi.pullback_id]
    rw [Phi.pullback_id]
    simp only [AddMonoidHom.id_apply, map_add, map_nsmul]
  · change data.rationalFunctions.pullback arrow.base
          (data.rationalFunctions.pullback left.hom.base
              right.hom.rationalFunction +
            right.hom.frobeniusDegree.val • left.hom.rationalFunction) =
        data.rationalFunctions.pullback (𝟙 (Object.base source))
            (data.rationalFunctions.pullback arrow.base
              right.hom.rationalFunction) +
          (1 : ℕ+).val • data.rationalFunctions.pullback arrow.base
            left.hom.rationalFunction
    have leftBase := left.baseIdentity
    change left.hom.base = 𝟙 (Object.base target) at leftBase
    have rightLinear := right.linear
    change right.hom.frobeniusDegree = 1 at rightLinear
    rw [leftBase, rightLinear, data.rationalFunctions.pullback_id]
    rw [data.rationalFunctions.pullback_id]
    simp only [AddMonoidHom.id_apply, map_add, map_nsmul]

/-- The multiplicative pullback map on `O^triangle`. -/
def linearEndomorphismPullbackHom
    {source target : Carrier Phi data} (arrow : source ⟶ target)
    (linear : (preFrobenioid Phi data).IsLinear arrow) :
    (preFrobenioid Phi data).LinearBaseIdentityEndomorphism target →*
      (preFrobenioid Phi data).LinearBaseIdentityEndomorphism source where
  toFun := linearEndomorphismPullback arrow linear
  map_one' := linearEndomorphismPullback_one arrow linear
  map_mul' := linearEndomorphismPullback_mul arrow linear

theorem linearEndomorphismPullbackHom_id
    (object : Carrier Phi data) :
    linearEndomorphismPullbackHom (𝟙 object)
        ((preFrobenioid Phi data).frobeniusDegree_id object) =
      MonoidHom.id
        ((preFrobenioid Phi data).LinearBaseIdentityEndomorphism object) := by
  apply MonoidHom.ext
  intro alpha
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  apply Hom.ext
  · exact alpha.linear.symm
  · exact alpha.baseIdentity.symm
  · change Phi.pullback (𝟙 (Object.base object)) alpha.hom.divisor =
      alpha.hom.divisor
    exact DFunLike.congr_fun (Phi.pullback_id (Object.base object)) _
  · change data.rationalFunctions.pullback (𝟙 (Object.base object))
        alpha.hom.rationalFunction = alpha.hom.rationalFunction
    exact DFunLike.congr_fun
      (data.rationalFunctions.pullback_id (Object.base object)) _

theorem linearEndomorphismPullbackHom_comp
    {first middle last : Carrier Phi data}
    (f : first ⟶ middle) (g : middle ⟶ last)
    (fLinear : (preFrobenioid Phi data).IsLinear f)
    (gLinear : (preFrobenioid Phi data).IsLinear g) :
    linearEndomorphismPullbackHom (f ≫ g) (by
        rw [PreFrobenioid.IsLinear,
          (preFrobenioid Phi data).frobeniusDegree_comp,
          fLinear, gLinear]
        simp) =
      (linearEndomorphismPullbackHom f fLinear).comp
        (linearEndomorphismPullbackHom g gLinear) := by
  apply MonoidHom.ext
  intro alpha
  apply PreFrobenioid.LinearBaseIdentityEndomorphism.ext
  apply Hom.ext
  · rfl
  · rfl
  · change Phi.pullback (f.base ≫ g.base) alpha.hom.divisor =
      Phi.pullback f.base (Phi.pullback g.base alpha.hom.divisor)
    exact DFunLike.congr_fun (Phi.pullback_comp f.base g.base) _
  · change data.rationalFunctions.pullback (f.base ≫ g.base)
        alpha.hom.rationalFunction =
      data.rationalFunctions.pullback f.base
        (data.rationalFunctions.pullback g.base alpha.hom.rationalFunction)
    exact DFunLike.congr_fun
      (data.rationalFunctions.pullback_comp f.base g.base) _

/-- Proposition 2.2(ii), (iv)'s rational-monoid transport in the model. -/
def rationalMonoidTransport :
    (preFrobenioid Phi data).RationalMonoidTransport where
  pullback f := linearEndomorphismPullbackHom f.hom f.linear
  pullback_id X := by
    simpa only [PreFrobenioid.isotropicLinear_id_hom] using
      linearEndomorphismPullbackHom_id (Phi := Phi) (data := data) X.obj
  pullback_comp f g := linearEndomorphismPullbackHom_comp
    f.hom g.hom f.linear g.linear
  hullInclusion object hull :=
    (unitTransport Phi data hull.hom hull.preStep).transport.toMonoidHom
  hullInclusion_injective object hull :=
    (unitTransport Phi data hull.hom hull.preStep).transport.injective

end

end Iut.SourceModelFrobenioid.Carrier
