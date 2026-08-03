/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.Orbicurve
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Two-cartesian squares of orbicurves

The cartesian diagrams in IUT I, Definition 3.1 are diagrams of stacks, hence
commute by invertible modifications and satisfy a bicategorical pullback
property. This file defines their 2-commutative squares and pseudo-cones.
-/

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open scoped SpecOfNotation

namespace Iut

universe u

/-- Forget the `K`-structure on a scheme over `K`, retaining its `F`-structure. -/
noncomputable def SchemeOverField.restrictScalars
    (F K : Type u) [Field F] [Field K] [Algebra F K] :
    SchemeOverField K ⥤ SchemeOverField F :=
  Over.map
    (Spec.map (CommRingCat.ofHom (algebraMap F K)))

/-- The induced pseudofunctor on opposite locally discrete scheme bicategories. -/
noncomputable def SchemeOverField.restrictScalarsPseudofunctor
    (F K : Type u) [Field F] [Field K] [Algebra F K] :
    LocallyDiscrete (SchemeOverField K)ᵒᵖ ⥤ᵖ
      LocallyDiscrete (SchemeOverField F)ᵒᵖ :=
  (SchemeOverField.restrictScalars F K).op.toPseudofunctor

/--
Scalar extension of an etale stack, identified with restriction along
`Sch/K -> Sch/F`.

The result is itself an `EtaleStackOverField K`, so its descent condition is
the actual etale stack predicate.
-/
structure EtaleStackScalarExtension
    (F K : Type u) [Field F] [Field K] [Algebra F K]
    (X : EtaleStackOverField F) where
  result : EtaleStackOverField K
  fiberEquivalence :
    Bicategory.Equivalence
      result.fiber
      (Pseudofunctor.comp
        (SchemeOverField.restrictScalarsPseudofunctor F K)
        X.fiber)

/--
Transport of certified orbicurve geometry along extension of scalars.

The target stack is the actual scalar extension, and each geometric invariant
is transported explicitly.  Consequently the target signature is derived;
it is not a freely supplied label.
-/
structure OrbicurveGeometryScalarExtension
    (F K : Type u) [Field F] [Field K] [Algebra F K]
    {sourceStack : EtaleStackOverField F}
    {targetStack : EtaleStackOverField K}
    (source : OrbicurveGeometry sourceStack)
    (target : OrbicurveGeometry targetStack)
    (stackExtension :
      EtaleStackScalarExtension F K sourceStack) where
  target_stack :
    targetStack = stackExtension.result
  compactificationGenus_preserved :
    target.signature.genus = source.signature.genus
  stackyOrders_preserved :
    target.signature.stackyOrders = source.signature.stackyOrders
  punctures_preserved :
    target.signature.punctures = source.signature.punctures

/-- Scalar extension of a hyperbolic orbicurve with transported geometry. -/
structure OrbicurveScalarExtension
    (F K : Type u) [Field F] [Field K] [Algebra F K]
    (X : HyperbolicOrbicurve F) where
  result : HyperbolicOrbicurve K
  stackExtension :
    EtaleStackScalarExtension F K X.stack
  geometryExtension :
    OrbicurveGeometryScalarExtension F K
      X.geometry result.geometry stackExtension

namespace OrbicurveScalarExtension

variable
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    {X : HyperbolicOrbicurve F}

/-- Scalar extension preserves the derived signature. -/
theorem signature_preserved
    (extension : OrbicurveScalarExtension F K X) :
    extension.result.signature = X.signature := by
  apply OrbicurveSignature.ext
  · exact extension.geometryExtension.compactificationGenus_preserved
  · exact extension.geometryExtension.stackyOrders_preserved
  · exact extension.geometryExtension.punctures_preserved

/-- The stack equivalence transported to the recorded result orbicurve. -/
noncomputable def fiberEquivalence
    (extension : OrbicurveScalarExtension F K X) :
    Bicategory.Equivalence
      extension.result.stack.fiber
      (Pseudofunctor.comp
        (SchemeOverField.restrictScalarsPseudofunctor F K)
        X.stack.fiber) := by
  rw [extension.geometryExtension.target_stack]
  exact extension.stackExtension.fiberEquivalence

end OrbicurveScalarExtension

/--
Scalar extension of a morphism of orbicurves, including comparison with the
original strong transformation after restriction of scalars.

The component and naturality equalities ensure that `restrictedMap` is the
actual precomposition of `map` with `Sch/K -> Sch/F`. The final 2-isomorphism
then identifies the local morphism with that precomposition through the chosen
stack equivalences.
-/
structure OrbicurveMorphismScalarExtension
    (F K : Type u) [Field F] [Field K] [Algebra F K]
    {X Y : HyperbolicOrbicurve F}
    (sourceExtension : OrbicurveScalarExtension F K X)
    (targetExtension : OrbicurveScalarExtension F K Y)
    (map : X.Hom Y) where
  result :
    sourceExtension.result.Hom targetExtension.result
  restrictedMap :
    Pseudofunctor.StrongTrans
      (Pseudofunctor.comp
        (SchemeOverField.restrictScalarsPseudofunctor F K)
        X.stack.fiber)
      (Pseudofunctor.comp
        (SchemeOverField.restrictScalarsPseudofunctor F K)
        Y.stack.fiber)
  restrictedMap_app :
    ∀ S,
      restrictedMap.app S =
        map.app
          ((SchemeOverField.restrictScalarsPseudofunctor
            F K).obj S)
  restrictedMap_naturality :
    ∀ {S T} (f : S ⟶ T),
      HEq (restrictedMap.naturality f)
        (map.naturality
          ((SchemeOverField.restrictScalarsPseudofunctor
            F K).map f))
  comparison :
    letI : Category
        (Pseudofunctor.StrongTrans
          sourceExtension.result.stack.fiber
          (Pseudofunctor.comp
            (SchemeOverField.restrictScalarsPseudofunctor F K)
            Y.stack.fiber)) :=
      Pseudofunctor.StrongTrans.homCategory
    Iso
      (Pseudofunctor.StrongTrans.vcomp result
        targetExtension.fiberEquivalence.hom)
      (Pseudofunctor.StrongTrans.vcomp
        sourceExtension.fiberEquivalence.hom
        restrictedMap)

/-- A 2-commutative square of hyperbolic orbicurves. -/
structure OrbicurveSquare
    {F : Type u} [Field F]
    (P X Y Z : HyperbolicOrbicurve F) where
  toX : P.Hom X
  toY : P.Hom Y
  xToBase : X.Hom Z
  yToBase : Y.Hom Z
  commutes :
    HyperbolicOrbicurve.Hom.TwoIso
      (Pseudofunctor.StrongTrans.vcomp toX xToBase)
      (Pseudofunctor.StrongTrans.vcomp toY yToBase)

namespace OrbicurveSquare

variable
    {F : Type u} [Field F]
    {P X Y Z : HyperbolicOrbicurve F}
    (square : OrbicurveSquare P X Y Z)

/-- A pseudo-cone from `W` to a 2-commutative square. -/
structure Cone (W : HyperbolicOrbicurve F) where
  toX : W.Hom X
  toY : W.Hom Y
  commutes :
    HyperbolicOrbicurve.Hom.TwoIso
      (Pseudofunctor.StrongTrans.vcomp toX square.xToBase)
      (Pseudofunctor.StrongTrans.vcomp toY square.yToBase)

/-- A morphism of pseudo-cones, including the compatibility with their 2-cells. -/
structure ConeMorphism
    {W : HyperbolicOrbicurve F}
    (source target : square.Cone W) where
  toX :
    HyperbolicOrbicurve.Hom.TwoCell source.toX target.toX
  toY :
    HyperbolicOrbicurve.Hom.TwoCell source.toY target.toY
  compatibility :
    Pseudofunctor.StrongTrans.whiskerRight
          toX square.xToBase ≫
        target.commutes.hom =
      source.commutes.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight
          toY square.yToBase

/--
The full bicategorical pullback universal property.

Essential surjectivity is represented by `lift`, `liftToX`, and `liftToY`.
Fullness is `liftTwoCell`: every compatible morphism of pseudo-cones lifts to
a 2-cell. `twoCell_ext` is faithfulness. Thus precomposition with the two legs
is an equivalence between the hom-category into `P` and the pseudo-cone
category, expressed without introducing a second category wrapper around the
same strong transformations.
-/
structure TwoPullbackWitness where
  lift :
    ∀ (W : HyperbolicOrbicurve F), square.Cone W → W.Hom P
  liftToX :
    ∀ (W : HyperbolicOrbicurve F) (cone : square.Cone W),
      HyperbolicOrbicurve.Hom.TwoIso
        (Pseudofunctor.StrongTrans.vcomp
          (lift W cone) square.toX)
        cone.toX
  liftToY :
    ∀ (W : HyperbolicOrbicurve F) (cone : square.Cone W),
      HyperbolicOrbicurve.Hom.TwoIso
        (Pseudofunctor.StrongTrans.vcomp
          (lift W cone) square.toY)
        cone.toY
  liftTwoCell :
    ∀ (W : HyperbolicOrbicurve F)
      (source target : square.Cone W),
      square.ConeMorphism source target →
        HyperbolicOrbicurve.Hom.TwoCell
          (lift W source) (lift W target)
  liftTwoCell_toX :
    ∀ (W : HyperbolicOrbicurve F)
      (source target : square.Cone W)
      (morphism : square.ConeMorphism source target),
      Pseudofunctor.StrongTrans.whiskerRight
          (liftTwoCell W source target morphism) square.toX =
        (liftToX W source).hom ≫
          morphism.toX ≫
            (liftToX W target).inv
  liftTwoCell_toY :
    ∀ (W : HyperbolicOrbicurve F)
      (source target : square.Cone W)
      (morphism : square.ConeMorphism source target),
      Pseudofunctor.StrongTrans.whiskerRight
          (liftTwoCell W source target morphism) square.toY =
        (liftToY W source).hom ≫
          morphism.toY ≫
            (liftToY W target).inv
  twoCell_ext :
    ∀ (W : HyperbolicOrbicurve F)
      {first second : W.Hom P}
      (alpha beta :
        HyperbolicOrbicurve.Hom.TwoCell first second),
      Pseudofunctor.StrongTrans.whiskerRight alpha square.toX =
          Pseudofunctor.StrongTrans.whiskerRight beta square.toX →
        Pseudofunctor.StrongTrans.whiskerRight alpha square.toY =
            Pseudofunctor.StrongTrans.whiskerRight beta square.toY →
          alpha = beta

end OrbicurveSquare

end Iut
