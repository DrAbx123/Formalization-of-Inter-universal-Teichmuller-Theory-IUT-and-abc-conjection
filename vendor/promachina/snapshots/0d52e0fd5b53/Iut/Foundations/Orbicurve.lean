/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Tactic

/-!
# Orbicurve source objects

This file supplies the stack- and Galois-category-level types needed to replace
the string-labelled orbicurves in the old finite model. It deliberately does
not assert that an arbitrary stack is algebraic or Deligne-Mumford: those
conditions require representability infrastructure that is not yet in mathlib
and remain named source obligations in the trace ledger.
-/

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped SpecOfNotation
open scoped Pseudofunctor.StrongTrans

namespace Iut

universe u

/--
The Galois group of the absolute separable closure of `F`, with its Krull
topology, as an actual profinite group.
-/
noncomputable abbrev AbsoluteGaloisProfinite
    (F : Type u) [Field F] : ProfiniteGrp.{u} :=
  InfiniteGalois.profiniteGalGrp F (SeparableClosure F)

/-- The category of schemes over `Spec(F)`. -/
noncomputable abbrev SchemeOverField (F : Type u) [CommRing F] :=
  Over (Spec(F))

/-- The big etale topology on schemes over `Spec(F)`. -/
noncomputable abbrev SchemeOverField.etaleTopology
    (F : Type u) [CommRing F] :
    GrothendieckTopology (SchemeOverField F) :=
  GrothendieckTopology.over AlgebraicGeometry.Scheme.etaleTopology (Spec(F))

/--
The signature `(g; m_1,...,m_r; n)` of an orbicurve: genus, stacky-point
orders, and ordinary punctures.
-/
structure OrbicurveSignature where
  genus : ℕ
  stackyOrders : List ℕ
  punctures : ℕ
  stackyOrders_ge_two : ∀ m ∈ stackyOrders, 2 ≤ m

namespace OrbicurveSignature

/-- Two signatures agree when their three geometric invariants agree. -/
@[ext]
theorem ext
    {source target : OrbicurveSignature}
    (genus : source.genus = target.genus)
    (stackyOrders : source.stackyOrders = target.stackyOrders)
    (punctures : source.punctures = target.punctures) :
    source = target := by
  cases source
  cases target
  simp_all

/-- Orbifold Euler characteristic `2 - 2g - n - sum_i (1 - 1/m_i)`. -/
noncomputable def eulerCharacteristic (signature : OrbicurveSignature) : ℚ :=
  2 - 2 * signature.genus - signature.punctures -
    (signature.stackyOrders.map fun m : ℕ => 1 - (1 : ℚ) / m).sum

/-- An orbicurve signature is hyperbolic when its orbifold Euler characteristic is negative. -/
def IsHyperbolic (signature : OrbicurveSignature) : Prop :=
  signature.eulerCharacteristic < 0

/-- The signature of a once-punctured elliptic curve. -/
def oncePuncturedElliptic : OrbicurveSignature where
  genus := 1
  stackyOrders := []
  punctures := 1
  stackyOrders_ge_two := by simp

theorem oncePuncturedElliptic_eulerCharacteristic :
    oncePuncturedElliptic.eulerCharacteristic = -1 := by
  norm_num [eulerCharacteristic, oncePuncturedElliptic]

theorem oncePuncturedElliptic_isHyperbolic :
    oncePuncturedElliptic.IsHyperbolic := by
  norm_num [IsHyperbolic, oncePuncturedElliptic_eulerCharacteristic]

end OrbicurveSignature

/--
A category-valued etale stack over a field.

The descent condition is mathlib's actual effective-descent predicate for
pseudofunctors into `Cat`. When the stack represents an orbicurve, its
canonical signature is stored here, making it an invariant of the represented
stack rather than metadata on a later wrapper.
-/
structure EtaleStackOverField (F : Type u) [CommRing F] where
  fiber :
    LocallyDiscrete (SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{u, u}
  isStack : fiber.IsStack (SchemeOverField.etaleTopology F)
  orbicurveSignature : Option OrbicurveSignature := none

/-- The bicategory in which category-valued etale stacks are diagrams. -/
abbrev EtaleStackPseudofunctor (F : Type u) [CommRing F] :=
  LocallyDiscrete (SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{u, u}

noncomputable instance EtaleStackPseudofunctor.homCategory
    {F : Type u} [CommRing F]
    (X Y : EtaleStackPseudofunctor F) :
    Category (Pseudofunctor.StrongTrans X Y) := by
  exact
    @Pseudofunctor.StrongTrans.homCategory
      (LocallyDiscrete (SchemeOverField F)ᵒᵖ) inferInstance
      Cat inferInstance X Y

/-- A morphism of etale stacks, represented by a strong transformation. -/
abbrev EtaleStackOverField.Hom
    {F : Type u} [CommRing F]
    (X Y : EtaleStackOverField F) :=
  Pseudofunctor.StrongTrans X.fiber Y.fiber

/--
The category-valued Yoneda functor represented by a scheme over `F`.

Its value at `U` is the discrete category of morphisms `U -> scheme`; its maps
are precomposition.  This lives in the orbicurve foundation file because
representability of a stack morphism is tested against these functors.
-/
noncomputable def schemeRepresentableFiberFunctor
    (F : Type u) [Field F]
    (scheme : SchemeOverField F) :
    (SchemeOverField F)ᵒᵖ ⥤ Cat.{u, u} where
  obj U :=
    Cat.of (Discrete (Opposite.unop U ⟶ scheme))
  map {U V} f :=
    (Discrete.functor
      (fun P : Opposite.unop U ⟶ scheme =>
        Discrete.mk (f.unop ≫ P))).toCatHom
  map_id U := by
    apply Cat.Hom.ext
    exact CategoryTheory.Functor.ext
      (fun P => by
        apply Discrete.ext
        simp)
      (by
        intro X Y f
        exact
          @Subsingleton.elim _
            (Discrete.instSubsingletonDiscreteHom _ _) _ _)
  map_comp f g := by
    apply Cat.Hom.ext
    exact CategoryTheory.Functor.ext
      (fun P => by
        apply Discrete.ext
        simp [Category.assoc])
      (by
        intro X Y f
        exact
          @Subsingleton.elim _
            (Discrete.instSubsingletonDiscreteHom _ _) _ _)

/-- The representable category-valued pseudofunctor attached to `scheme`. -/
noncomputable def schemeRepresentableEtalePseudofunctor
    (F : Type u) [Field F]
    (scheme : SchemeOverField F) :
    EtaleStackPseudofunctor F :=
  (schemeRepresentableFiberFunctor F scheme).toPseudofunctor'

/--
A strong transformation between representable etale pseudofunctors which is
certified to be induced by one actual morphism of schemes over `F`.
-/
structure SchemeRepresentableMap
    {F : Type u} [Field F]
    {source target : SchemeOverField F}
    (map : source ⟶ target) where
  transformation :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F source)
      (schemeRepresentableEtalePseudofunctor F target)
  app_eq :
    ∀ U,
      transformation.app (LocallyDiscrete.mk U) =
        (Discrete.functor
          (fun P : Opposite.unop U ⟶ source =>
            Discrete.mk (P ≫ map))).toCatHom

/-- A 2-commutative square of category-valued etale pseudofunctors. -/
structure EtalePseudofunctorSquare
    {F : Type u} [Field F]
    (P X Y Z : EtaleStackPseudofunctor F) where
  toX : Pseudofunctor.StrongTrans P X
  toY : Pseudofunctor.StrongTrans P Y
  xToBase : Pseudofunctor.StrongTrans X Z
  yToBase : Pseudofunctor.StrongTrans Y Z
  commutes :
    Iso
      (Pseudofunctor.StrongTrans.vcomp toX xToBase)
      (Pseudofunctor.StrongTrans.vcomp toY yToBase)

namespace EtalePseudofunctorSquare

variable
    {F : Type u} [Field F]
    {P X Y Z : EtaleStackPseudofunctor F}
    (square : EtalePseudofunctorSquare P X Y Z)

/-- A pseudo-cone from `W` to a 2-commutative square. -/
structure Cone (W : EtaleStackPseudofunctor F) where
  toX : Pseudofunctor.StrongTrans W X
  toY : Pseudofunctor.StrongTrans W Y
  commutes :
    Iso
      (Pseudofunctor.StrongTrans.vcomp toX square.xToBase)
      (Pseudofunctor.StrongTrans.vcomp toY square.yToBase)

/-- A morphism between two pseudo-cones. -/
structure ConeMorphism
    {W : EtaleStackPseudofunctor F}
    (source target : square.Cone W) where
  toX : source.toX ⟶ target.toX
  toY : source.toY ⟶ target.toY
  compatibility :
    Pseudofunctor.StrongTrans.whiskerRight
          toX square.xToBase ≫
        target.commutes.hom =
      source.commutes.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight
          toY square.yToBase

/--
The full bicategorical pullback universal property for a square of etale
pseudofunctors.
-/
structure TwoPullbackWitness where
  lift :
    ∀ (W : EtaleStackPseudofunctor F), square.Cone W →
      Pseudofunctor.StrongTrans W P
  liftToX :
    ∀ (W : EtaleStackPseudofunctor F) (cone : square.Cone W),
      Iso
        (Pseudofunctor.StrongTrans.vcomp
          (lift W cone) square.toX)
        cone.toX
  liftToY :
    ∀ (W : EtaleStackPseudofunctor F) (cone : square.Cone W),
      Iso
        (Pseudofunctor.StrongTrans.vcomp
          (lift W cone) square.toY)
        cone.toY
  liftTwoCell :
    ∀ (W : EtaleStackPseudofunctor F)
      (source target : square.Cone W),
      square.ConeMorphism source target →
        (lift W source ⟶ lift W target)
  liftTwoCell_toX :
    ∀ (W : EtaleStackPseudofunctor F)
      (source target : square.Cone W)
      (morphism : square.ConeMorphism source target),
      Pseudofunctor.StrongTrans.whiskerRight
          (liftTwoCell W source target morphism) square.toX =
        (liftToX W source).hom ≫
          morphism.toX ≫
            (liftToX W target).inv
  liftTwoCell_toY :
    ∀ (W : EtaleStackPseudofunctor F)
      (source target : square.Cone W)
      (morphism : square.ConeMorphism source target),
      Pseudofunctor.StrongTrans.whiskerRight
          (liftTwoCell W source target morphism) square.toY =
        (liftToY W source).hom ≫
          morphism.toY ≫
            (liftToY W target).inv
  twoCell_ext :
    ∀ (W : EtaleStackPseudofunctor F)
      {first second : Pseudofunctor.StrongTrans W P}
      (alpha beta : first ⟶ second),
      Pseudofunctor.StrongTrans.whiskerRight alpha square.toX =
          Pseudofunctor.StrongTrans.whiskerRight beta square.toX →
        Pseudofunctor.StrongTrans.whiskerRight alpha square.toY =
            Pseudofunctor.StrongTrans.whiskerRight beta square.toY →
          alpha = beta

end EtalePseudofunctorSquare

/--
A scheme presentation of one base change of a stack morphism.  The square is
required to be a genuine bicategorical pullback, and its projection is tied to
an actual scheme morphism rather than to an unrelated transformation.
-/
structure EtaleStackBaseChangePresentation
    {F : Type u} [Field F]
    {source target : EtaleStackOverField F}
    (map : source.Hom target)
    (testScheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F testScheme)
        target.fiber) where
  pullbackScheme : SchemeOverField F
  projection : pullbackScheme ⟶ testScheme
  projectionMap : SchemeRepresentableMap projection
  toSource :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F pullbackScheme)
      source.fiber
  commutes :
    Iso
      (Pseudofunctor.StrongTrans.vcomp toSource map)
      (Pseudofunctor.StrongTrans.vcomp
        projectionMap.transformation point)
  isPullback :
    (EtalePseudofunctorSquare.mk
      toSource projectionMap.transformation map point commutes).TwoPullbackWitness

/--
A representable property of a stack morphism, checked on every scheme-valued
point by an actual scheme-theoretic base change.
-/
structure EtaleStackRepresentableMorphismProperty
    {F : Type u} [Field F]
    (property : ∀ {S T : Scheme.{u}}, (S ⟶ T) → Prop)
    {source target : EtaleStackOverField F}
    (map : source.Hom target) where
  baseChange :
    ∀ (testScheme : SchemeOverField F)
      (point :
        Pseudofunctor.StrongTrans
          (schemeRepresentableEtalePseudofunctor F testScheme)
          target.fiber),
      EtaleStackBaseChangePresentation map testScheme point
  hasProperty :
    ∀ (testScheme : SchemeOverField F)
      (point :
        Pseudofunctor.StrongTrans
          (schemeRepresentableEtalePseudofunctor F testScheme)
          target.fiber),
      property (baseChange testScheme point).projection.left

/-- Representable finite-etale morphisms of etale stacks. -/
abbrev EtaleStackFiniteEtaleMorphism
    {F : Type u} [Field F]
    {source target : EtaleStackOverField F}
    (map : source.Hom target) :=
  EtaleStackRepresentableMorphismProperty
    (fun f => AlgebraicGeometry.IsFinite f ∧ AlgebraicGeometry.Etale f)
    map

/-- Representable open immersions of etale stacks. -/
abbrev EtaleStackOpenImmersion
    {F : Type u} [Field F]
    {source target : EtaleStackOverField F}
    (map : source.Hom target) :=
  EtaleStackRepresentableMorphismProperty
    (fun f => AlgebraicGeometry.IsOpenImmersion f)
    map

/--
Certificate exposing the canonical orbicurve signature already carried by a
represented etale stack and proving that geometry hyperbolic.
-/
structure OrbicurveGeometry
    {F : Type u} [Field F]
    (stack : EtaleStackOverField F) where
  signature : OrbicurveSignature
  realizes_signature : stack.orbicurveSignature = some signature
  hyperbolic : signature.IsHyperbolic

namespace OrbicurveGeometry

/-- A represented stack has at most one certified orbicurve signature. -/
theorem signature_eq
    {F : Type u} [Field F]
    {stack : EtaleStackOverField F}
    (first second : OrbicurveGeometry stack) :
    first.signature = second.signature := by
  apply Option.some.inj
  exact first.realizes_signature.symm.trans second.realizes_signature

end OrbicurveGeometry

/--
A hyperbolic orbicurve over `F`: a represented stack together with the
certificate exposing its canonical geometry. A second certificate for the
same stack is forced to have the same signature.
-/
structure HyperbolicOrbicurve (F : Type u) [Field F] where
  stack : EtaleStackOverField F
  geometry : OrbicurveGeometry stack

namespace HyperbolicOrbicurve

/-- The signature derived from the orbicurve's certified geometry. -/
def signature
    {F : Type u} [Field F]
    (X : HyperbolicOrbicurve F) : OrbicurveSignature :=
  X.geometry.signature

/-- Hyperbolicity follows from the certified geometry. -/
theorem hyperbolic
    {F : Type u} [Field F]
    (X : HyperbolicOrbicurve F) : X.signature.IsHyperbolic :=
  X.geometry.hyperbolic

/-- Two wrappers of the same represented stack cannot advertise incompatible signatures. -/
theorem signature_eq_of_stack_eq
    {F : Type u} [Field F]
    {X Y : HyperbolicOrbicurve F}
    (sameStack : X.stack = Y.stack) : X.signature = Y.signature := by
  cases X with
  | mk xStack xGeometry =>
      cases Y with
      | mk yStack yGeometry =>
          dsimp only at sameStack ⊢
          subst yStack
          exact xGeometry.signature_eq yGeometry

/-- Negative form: incompatible type claims cannot share a represented stack. -/
theorem no_incompatible_signature_on_same_stack
    {F : Type u} [Field F]
    {X Y : HyperbolicOrbicurve F}
    (sameStack : X.stack = Y.stack)
    (incompatible : X.signature ≠ Y.signature) : False :=
  incompatible (signature_eq_of_stack_eq sameStack)

end HyperbolicOrbicurve

/-- A morphism of hyperbolic orbicurves is a morphism of their etale stacks. -/
abbrev HyperbolicOrbicurve.Hom
    {F : Type u} [Field F]
    (X Y : HyperbolicOrbicurve F) :=
  X.stack.Hom Y.stack

/-- An invertible modification between two orbicurve morphisms. -/
abbrev HyperbolicOrbicurve.Hom.TwoIso
    {F : Type u} [Field F]
    {X Y : HyperbolicOrbicurve F}
    (f g : X.Hom Y) :=
  Iso f g

/-- A modification between orbicurve morphisms. -/
abbrev HyperbolicOrbicurve.Hom.TwoCell
    {F : Type u} [Field F]
    {X Y : HyperbolicOrbicurve F}
    (f g : X.Hom Y) :=
  Pseudofunctor.StrongTrans.Hom f g

namespace HyperbolicOrbicurve.Hom.TwoCell

variable
    {F : Type u} [Field F]
    {X Y : HyperbolicOrbicurve F}
    {f g h : X.Hom Y}

def id (f : X.Hom Y) :
    HyperbolicOrbicurve.Hom.TwoCell f f :=
  ⟨Pseudofunctor.StrongTrans.Modification.id f⟩

def comp
    (first : HyperbolicOrbicurve.Hom.TwoCell f g)
    (second : HyperbolicOrbicurve.Hom.TwoCell g h) :
    HyperbolicOrbicurve.Hom.TwoCell f h :=
  ⟨Pseudofunctor.StrongTrans.Modification.vcomp
    first.as second.as⟩

end HyperbolicOrbicurve.Hom.TwoCell

/-- The identity morphism of a hyperbolic orbicurve. -/
noncomputable def HyperbolicOrbicurve.Hom.id
    {F : Type u} [Field F]
    (X : HyperbolicOrbicurve F) :
    X.Hom X :=
  Pseudofunctor.StrongTrans.id X.stack.fiber

/-- Composition of morphisms of hyperbolic orbicurves. -/
noncomputable def HyperbolicOrbicurve.Hom.comp
    {F : Type u} [Field F]
    {X Y Z : HyperbolicOrbicurve F}
    (f : X.Hom Y) (g : Y.Hom Z) :
    X.Hom Z :=
  Pseudofunctor.StrongTrans.vcomp f g

/-- Transport an orbicurve morphism along equalities of its source and target. -/
noncomputable def HyperbolicOrbicurve.Hom.cast
    {F : Type u} [Field F]
    {X X' Y Y' : HyperbolicOrbicurve F}
    (source_eq : X = X') (target_eq : Y = Y')
    (f : X.Hom Y) :
    X'.Hom Y' := by
  subst X'
  subst Y'
  exact f

/--
An object of the finite-etale-cover category of an orbicurve.  Its source is
an etale stack, its arrow lands in the represented stack of `X`, and finite
etaleness is the representable base-change property above.
-/
structure OrbicurveFiniteEtaleCover
    {F : Type u} [Field F]
    (X : HyperbolicOrbicurve F) where
  source : EtaleStackOverField F
  map : source.Hom X.stack
  finiteEtale : EtaleStackFiniteEtaleMorphism map

/-- An actual morphism over `X` between two represented finite-etale covers. -/
structure OrbicurveFiniteEtaleCoverMap
    {F : Type u} [Field F]
    {X : HyperbolicOrbicurve F}
    (source target : OrbicurveFiniteEtaleCover X) where
  map : source.source.Hom target.source
  commutes :
    Iso
      (Pseudofunctor.StrongTrans.vcomp map target.map)
      source.map

namespace OrbicurveFiniteEtaleCover

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}

/-- The object of a stack selected by a scheme-valued point at its own scheme. -/
noncomputable def pointObject
    {stack : EtaleStackOverField F}
    (scheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F scheme)
        stack.fiber) :
    stack.fiber.obj
      (LocallyDiscrete.mk (Opposite.op scheme)) :=
  (point.app (LocallyDiscrete.mk (Opposite.op scheme))).toFunctor.obj
    (Discrete.mk (𝟙 scheme))

/-- The literal fiber category of a cover at a scheme-valued point. -/
abbrev GeometricFiber
    (scheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F scheme)
        X.stack.fiber)
    (cover : OrbicurveFiniteEtaleCover X) :=
  CostructuredArrow
    (cover.map.app
      (LocallyDiscrete.mk (Opposite.op scheme))).toFunctor
    (pointObject scheme point)


end OrbicurveFiniteEtaleCover

/--
A geometric cusp of `X`, represented as a point on a compactification which
does not lie in the image of the open orbicurve.  The open map is required to
be representably an open immersion, so the boundary condition refers to the
actual compactification rather than to a label.
-/
structure OrbicurveBoundaryCusp
    {F : Type u} [Field F]
    (X : HyperbolicOrbicurve F) where
  compactification : EtaleStackOverField F
  openMap : X.stack.Hom compactification
  openImmersion : EtaleStackOpenImmersion openMap
  residueScheme : SchemeOverField F
  point :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F residueScheme)
      compactification.fiber
  isBoundary :
    ∀ object :
      X.stack.fiber.obj
        (LocallyDiscrete.mk (Opposite.op residueScheme)),
      IsEmpty
        ((openMap.app
            (LocallyDiscrete.mk (Opposite.op residueScheme))).toFunctor.obj
              object ≅
          OrbicurveFiniteEtaleCover.pointObject residueScheme point)

/-- The order-two group that acts by elliptic inversion. -/
abbrev SignGroup :=
  Multiplicative (ZMod 2)

/-- The one-object bicategory indexing a coherent sign action. -/
abbrev SignActionIndex :=
  LocallyDiscrete (SingleObj SignGroup)

/-- The unique object of the sign-action indexing bicategory. -/
def signActionObject : SignActionIndex :=
  LocallyDiscrete.mk (Quiver.SingleObj.star SignGroup)

/-- The nontrivial element of the sign group. -/
def signActionGenerator :
    signActionObject ⟶ signActionObject :=
  ⟨Multiplicative.ofAdd (1 : ZMod 2)⟩

/--
A coherent action of the sign group on an orbicurve stack.

The pseudofunctor supplies the unit, multiplication, and associativity
coherences. `generator_identification` identifies its nontrivial arrow with
the chosen elliptic inversion on `X`.
-/
structure OrbicurveSignAction
    {F : Type u} [Field F]
    (X : HyperbolicOrbicurve F) where
  diagram :
    SignActionIndex ⥤ᵖ
      EtaleStackPseudofunctor F
  atBase :
    Bicategory.Equivalence
      (diagram.obj signActionObject) X.stack.fiber
  inversion : X.Hom X
  generator_identification :
    (atBase.inv ≫ diagram.map signActionGenerator) ≫
        atBase.hom ≅
      inversion
  inversionSquared :
    HyperbolicOrbicurve.Hom.TwoIso
      (HyperbolicOrbicurve.Hom.comp inversion inversion)
      (HyperbolicOrbicurve.Hom.id X)

namespace OrbicurveSignAction

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}
variable (action : OrbicurveSignAction X)

/-- The coherence for composing two copies of the nontrivial sign arrow. -/
def generatorSquareComparison :
    action.diagram.map
        (signActionGenerator ≫ signActionGenerator) ≅
      action.diagram.map signActionGenerator ≫
        action.diagram.map signActionGenerator :=
  action.diagram.mapComp
    signActionGenerator signActionGenerator

end OrbicurveSignAction

/--
A morphism out of an orbicurve that is equivariant for its sign action.

The cocycle equation says that applying the invariant 2-isomorphism twice is
the identity after identifying two inversions with the identity action.
-/
structure OrbicurveSignInvariantMorphism
    {F : Type u} [Field F]
    {X : HyperbolicOrbicurve F}
    (action : OrbicurveSignAction X)
    (Y : HyperbolicOrbicurve F) where
  map : X.Hom Y
  invariant :
    HyperbolicOrbicurve.Hom.TwoIso
      (HyperbolicOrbicurve.Hom.comp action.inversion map)
      map
  cocycle :
    (Pseudofunctor.StrongTrans.associator
          action.inversion action.inversion map).hom ≫
        Pseudofunctor.StrongTrans.whiskerLeft
          action.inversion invariant.hom ≫
        invariant.hom =
      Pseudofunctor.StrongTrans.whiskerRight
          action.inversionSquared.hom map ≫
        (Pseudofunctor.StrongTrans.leftUnitor map).hom

namespace OrbicurveSignInvariantMorphism

variable
    {F : Type u} [Field F]
    {X Y : HyperbolicOrbicurve F}
    {action : OrbicurveSignAction X}

/-- A 2-cell compatible with the sign-invariance structures. -/
structure Hom
    (source target : OrbicurveSignInvariantMorphism action Y) where
  app :
    HyperbolicOrbicurve.Hom.TwoCell source.map target.map
  equivariant :
    Pseudofunctor.StrongTrans.whiskerLeft
          action.inversion app ≫
        target.invariant.hom =
      source.invariant.hom ≫ app

end OrbicurveSignInvariantMorphism

/--
The bicategorical universal property of the quotient of `X` by its sign
action.

Every coherent invariant map out of `X` descends through `quotient`. Every
compatible 2-cell descends, and equality can be checked after precomposition
with `quotient`. These are essential surjectivity, fullness, and faithfulness
of the functor from maps out of the quotient to invariant maps out of `X`.
-/
structure OrbicurveSignQuotientWitness
    {F : Type u} [Field F]
    {X C : HyperbolicOrbicurve F}
    (action : OrbicurveSignAction X)
    (quotient :
      OrbicurveSignInvariantMorphism action C) where
  descend :
    ∀ (Y : HyperbolicOrbicurve F),
      OrbicurveSignInvariantMorphism action Y →
        C.Hom Y
  factor :
    ∀ (Y : HyperbolicOrbicurve F)
      (invariant :
        OrbicurveSignInvariantMorphism action Y),
      HyperbolicOrbicurve.Hom.TwoIso
        (HyperbolicOrbicurve.Hom.comp
          quotient.map (descend Y invariant))
        invariant.map
  descendTwoCell :
    ∀ (Y : HyperbolicOrbicurve F)
      (source target :
        OrbicurveSignInvariantMorphism action Y),
      OrbicurveSignInvariantMorphism.Hom source target →
        HyperbolicOrbicurve.Hom.TwoCell
          (descend Y source) (descend Y target)
  descendTwoCell_factor :
    ∀ (Y : HyperbolicOrbicurve F)
      (source target :
        OrbicurveSignInvariantMorphism action Y)
      (alpha :
        OrbicurveSignInvariantMorphism.Hom source target),
      Pseudofunctor.StrongTrans.whiskerLeft
          quotient.map
          (descendTwoCell Y source target alpha) =
        (factor Y source).hom ≫ alpha.app ≫
          (factor Y target).inv
  twoCell_ext :
    ∀ (Y : HyperbolicOrbicurve F)
      {first second : C.Hom Y}
      (alpha beta :
        HyperbolicOrbicurve.Hom.TwoCell first second),
      Pseudofunctor.StrongTrans.whiskerLeft
          quotient.map alpha =
          Pseudofunctor.StrongTrans.whiskerLeft
            quotient.map beta →
        alpha = beta

/--
A chosen fiber functor and certified profinite fundamental group for a Galois
category of finite etale covers.
-/
structure EtaleFundamentalGroup where
  Cover : Type (u + 1)
  coverCategory : Category.{u} Cover
  galoisCategory : @GaloisCategory Cover coverCategory
  fiber : letI := coverCategory; Cover ⥤ FintypeCat.{u}
  fiberFunctor :
    letI := coverCategory
    letI := galoisCategory
    PreGaloisCategory.FiberFunctor fiber
  group : ProfiniteGrp.{u}
  action :
    letI := coverCategory
    letI := galoisCategory
    letI := fiberFunctor
    ∀ X : Cover, MulAction group (fiber.obj X)
  isFundamentalGroup :
    letI := coverCategory
    letI := galoisCategory
    letI := fiberFunctor
    letI (X : Cover) := action X
    PreGaloisCategory.IsFundamentalGroup fiber group

namespace EtaleFundamentalGroup

/-- The stored profinite group is the fundamental group of the stored fiber functor. -/
theorem certified (data : EtaleFundamentalGroup) :
    letI := data.coverCategory
    letI := data.galoisCategory
    letI := data.fiberFunctor
    letI (X : data.Cover) := data.action X
    PreGaloisCategory.IsFundamentalGroup data.fiber data.group :=
  data.isFundamentalGroup

end EtaleFundamentalGroup

namespace OrbicurveFiniteEtaleCover

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}

/--
The map on a geometric fiber induced by a stack morphism over `X` and its
commuting 2-cell.
-/
noncomputable def geometricFiberMap
    {source target : OrbicurveFiniteEtaleCover X}
    (map : source.source.Hom target.source)
    (commutes :
      Iso
        (Pseudofunctor.StrongTrans.vcomp map target.map)
        source.map)
    (scheme : SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor F scheme)
        X.stack.fiber) :
    GeometricFiber scheme point source ⥤
      GeometricFiber scheme point target := by
  let site := LocallyDiscrete.mk (Opposite.op scheme)
  let component :
      map.app site ≫ target.map.app site ⟶
        source.map.app site :=
    eqToHom
        (Pseudofunctor.StrongTrans.comp_app
          map target.map site).symm ≫
      commutes.hom.as.app site
  let alpha :
      (map.app site).toFunctor ⋙
          (target.map.app site).toFunctor ⟶
        (source.map.app site).toFunctor ⋙
          𝟭 (X.stack.fiber.obj site) := by
    simpa using component.toNatTrans
  exact CostructuredArrow.map₂
    (F := (map.app site).toFunctor)
    (U := (target.map.app site).toFunctor)
    (S := (source.map.app site).toFunctor)
    (G := 𝟭 (X.stack.fiber.obj site))
    alpha
    (𝟙 (pointObject scheme point))

end OrbicurveFiniteEtaleCover

/--
The finite-etale Galois category of one represented orbicurve with a chosen
geometric fiber functor and a fixed certified fundamental group.

Unlike `EtaleFundamentalGroup`, the cover type is not caller-selected: it is
the type of representably finite-etale stack maps to `X`.  Every categorical
arrow is also realized by an actual stack morphism over `X`, and the chosen
fiber functor is identified, naturally, with the literal geometric fibers.
-/
structure OrbicurveEtaleFundamentalGroup
    {F : Type u} [Field F]
    (X : HyperbolicOrbicurve F)
    (group : ProfiniteGrp.{u}) where
  coverCategory : Category.{u} (OrbicurveFiniteEtaleCover X)
  galoisCategory :
    letI := coverCategory
    @GaloisCategory (OrbicurveFiniteEtaleCover X) coverCategory
  baseScheme : SchemeOverField F
  basePoint :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor F baseScheme)
      X.stack.fiber
  fiber :
    letI := coverCategory
    OrbicurveFiniteEtaleCover X ⥤ FintypeCat.{u}
  fiberFunctor :
    letI := coverCategory
    letI := galoisCategory
    PreGaloisCategory.FiberFunctor fiber
  coverMorphism :
    letI := coverCategory
    ∀ {source target : OrbicurveFiniteEtaleCover X},
      (source ⟶ target) → source.source.Hom target.source
  coverMorphism_over :
    letI := coverCategory
    ∀ {source target : OrbicurveFiniteEtaleCover X}
      (map : source ⟶ target),
      Iso
        (Pseudofunctor.StrongTrans.vcomp
          (coverMorphism map) target.map)
        source.map
  coverMorphism_bijective :
    letI := coverCategory
    ∀ {source target : OrbicurveFiniteEtaleCover X},
      Function.Bijective
        (fun map : source ⟶ target =>
          ({ map := coverMorphism map
             commutes := coverMorphism_over map } :
            OrbicurveFiniteEtaleCoverMap source target))
  coverMorphism_id :
    letI := coverCategory
    ∀ (cover : OrbicurveFiniteEtaleCover X),
      Iso
        (coverMorphism (𝟙 cover))
        (Pseudofunctor.StrongTrans.id cover.source.fiber)
  coverMorphism_comp :
    letI := coverCategory
    ∀ {first second third : OrbicurveFiniteEtaleCover X}
      (f : first ⟶ second) (g : second ⟶ third),
      Iso
        (coverMorphism (f ≫ g))
        (Pseudofunctor.StrongTrans.vcomp
          (coverMorphism f) (coverMorphism g))
  geometricFiberFintype :
    ∀ cover : OrbicurveFiniteEtaleCover X,
      Fintype
        (OrbicurveFiniteEtaleCover.GeometricFiber
          baseScheme basePoint cover)
  fiberIdentification :
    ∀ cover : OrbicurveFiniteEtaleCover X,
      (fiber.obj cover).obj ≃
        OrbicurveFiniteEtaleCover.GeometricFiber
          baseScheme basePoint cover
  fiberIdentification_natural :
    letI := coverCategory
    ∀ {source target : OrbicurveFiniteEtaleCover X}
      (map : source ⟶ target) (element : (fiber.obj source).obj),
      fiberIdentification target (fiber.map map element) =
        (OrbicurveFiniteEtaleCover.geometricFiberMap
          (coverMorphism map) (coverMorphism_over map)
          baseScheme basePoint).obj
            (fiberIdentification source element)
  action :
    letI := coverCategory
    letI := galoisCategory
    letI := fiberFunctor
    ∀ cover : OrbicurveFiniteEtaleCover X,
      MulAction group (fiber.obj cover)
  isFundamentalGroup :
    letI := coverCategory
    letI := galoisCategory
    letI := fiberFunctor
    letI (cover : OrbicurveFiniteEtaleCover X) := action cover
    PreGaloisCategory.IsFundamentalGroup fiber group

namespace OrbicurveEtaleFundamentalGroup

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}
variable {G : ProfiniteGrp.{u}}

/-- Forget only the geometric realization, retaining the certified Galois category. -/
noncomputable def toEtaleFundamentalGroup
    (data : OrbicurveEtaleFundamentalGroup X G) :
    EtaleFundamentalGroup where
  Cover := OrbicurveFiniteEtaleCover X
  coverCategory := data.coverCategory
  galoisCategory := data.galoisCategory
  fiber := data.fiber
  fiberFunctor := data.fiberFunctor
  group := G
  action := data.action
  isFundamentalGroup := data.isFundamentalGroup

/-- The fixed group certified by the orbicurve's geometric fiber functor. -/
def group
    (_data : OrbicurveEtaleFundamentalGroup X G) :
    ProfiniteGrp.{u} :=
  G

end OrbicurveEtaleFundamentalGroup

/-- An actual open embedding in the category of profinite groups. -/
structure ProfiniteOpenEmbedding (source target : ProfiniteGrp.{u}) where
  hom : source ⟶ target
  isOpenEmbedding : Topology.IsOpenEmbedding hom

namespace ProfiniteOpenEmbedding

variable {source middle target : ProfiniteGrp.{u}}

theorem injective (embedding : ProfiniteOpenEmbedding source target) :
    Function.Injective embedding.hom :=
  embedding.isOpenEmbedding.injective

theorem open_range (embedding : ProfiniteOpenEmbedding source target) :
    IsOpen (Set.range embedding.hom) :=
  embedding.isOpenEmbedding.isOpen_range

/-- Composition preserves the open-embedding condition. -/
def comp
    (first : ProfiniteOpenEmbedding source middle)
    (second : ProfiniteOpenEmbedding middle target) :
    ProfiniteOpenEmbedding source target where
  hom := first.hom ≫ second.hom
  isOpenEmbedding := by
    simpa [Function.comp_def] using
      second.isOpenEmbedding.comp first.isOpenEmbedding

end ProfiniteOpenEmbedding

/--
An injective morphism of profinite groups.

Unlike `ProfiniteOpenEmbedding`, this is the appropriate notion for local
decomposition groups inside an absolute Galois group: their images are closed,
but need not be open.
-/
structure ProfiniteEmbedding (source target : ProfiniteGrp.{u}) where
  hom : source ⟶ target
  injective : Function.Injective hom

namespace ProfiniteEmbedding

variable {source middle target : ProfiniteGrp.{u}}

/-- Composition of injective continuous profinite-group morphisms. -/
def comp
    (first : ProfiniteEmbedding source middle)
    (second : ProfiniteEmbedding middle target) :
    ProfiniteEmbedding source target where
  hom := first.hom ≫ second.hom
  injective := second.injective.comp first.injective

end ProfiniteEmbedding

/-- A closed subgroup with its induced topology, regarded as a profinite group. -/
def closedSubgroupProfiniteGrp
    {G : ProfiniteGrp.{u}} (subgroup : ClosedSubgroup G) :
    ProfiniteGrp.{u} :=
  ProfiniteGrp.ofClosedSubgroup subgroup

/-- The canonical continuous injective morphism from a closed subgroup. -/
def closedSubgroupProfiniteInclusion
    {G : ProfiniteGrp.{u}} (subgroup : ClosedSubgroup G) :
    ProfiniteEmbedding (closedSubgroupProfiniteGrp subgroup) G := by
  letI : IsTopologicalGroup subgroup :=
    inferInstanceAs (IsTopologicalGroup subgroup.toSubgroup)
  change ProfiniteEmbedding (ProfiniteGrp.of subgroup) G
  refine
    { hom := ProfiniteGrp.ofHom
        ⟨subgroup.toSubgroup.subtype, continuous_subtype_val⟩
      injective := ?_ }
  exact Subtype.val_injective

/-- The closed kernel of a continuous morphism of profinite groups. -/
def profiniteKernelClosedSubgroup
    {source target : ProfiniteGrp.{u}}
    (projection : source ⟶ target) :
    ClosedSubgroup source where
  toSubgroup := projection.hom.ker
  isClosed' := by
    change IsClosed (projection ⁻¹' {1})
    exact isClosed_singleton.preimage projection.hom.continuous

/-- Restrict a profinite-group morphism to a closed subgroup of its source. -/
noncomputable def profiniteClosedSubgroupRestriction
    {source target : ProfiniteGrp.{u}}
    (subgroup : ClosedSubgroup source)
    (map : source ⟶ target) :
    closedSubgroupProfiniteGrp subgroup ⟶ target :=
  (closedSubgroupProfiniteInclusion subgroup).hom ≫ map

/--
The kernel of a morphism restricted to a closed subgroup embeds canonically in
the kernel of the original morphism.
-/
noncomputable def profiniteRestrictedKernelEmbedding
    {source target : ProfiniteGrp.{u}}
    (subgroup : ClosedSubgroup source)
    (map : source ⟶ target) :
    ProfiniteEmbedding
      (closedSubgroupProfiniteGrp
        (profiniteKernelClosedSubgroup
          (profiniteClosedSubgroupRestriction subgroup map)))
      (closedSubgroupProfiniteGrp
        (profiniteKernelClosedSubgroup map)) := by
  let restricted := profiniteClosedSubgroupRestriction subgroup map
  let restrictedKernel := profiniteKernelClosedSubgroup restricted
  let ambientKernel := profiniteKernelClosedSubgroup map
  letI : IsTopologicalGroup restrictedKernel :=
    inferInstanceAs (IsTopologicalGroup restrictedKernel.toSubgroup)
  letI : IsTopologicalGroup ambientKernel :=
    inferInstanceAs (IsTopologicalGroup ambientKernel.toSubgroup)
  change ProfiniteEmbedding
    (ProfiniteGrp.of restrictedKernel) (ProfiniteGrp.of ambientKernel)
  let inclusion : restrictedKernel →* ambientKernel :=
    { toFun := fun element =>
        ⟨element.1.1, by
          change map element.1.1 = 1
          have inKernel := element.property
          change restricted element = 1 at inKernel
          exact inKernel⟩
      map_one' := rfl
      map_mul' := by intros; rfl }
  refine
    { hom := ProfiniteGrp.ofHom ⟨inclusion, ?_⟩
      injective := ?_ }
  · exact
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro first second equality
    change inclusion first = inclusion second at equality
    have ambientEquality :
        (first.1.1 : source) = second.1.1 :=
      congrArg (fun element : ambientKernel => (element.1 : source)) equality
    exact Subtype.ext (Subtype.ext ambientEquality)

/--
An exact sequence `1 -> geometric -> arithmetic -> Galois -> 1` of profinite
groups. Exactness is an equality of the actual range and kernel subgroups.
-/
structure ProfiniteFundamentalExactSequence
    (geometric arithmetic galois : ProfiniteGrp.{u}) where
  inclusion : geometric ⟶ arithmetic
  projection : arithmetic ⟶ galois
  inclusion_injective : Function.Injective inclusion
  projection_surjective : Function.Surjective projection
  exact : inclusion.hom.range = projection.hom.ker

namespace ProfiniteFundamentalExactSequence

variable {geometric arithmetic galois : ProfiniteGrp.{u}}
variable (sequence :
  ProfiniteFundamentalExactSequence geometric arithmetic galois)

theorem projection_comp_inclusion_eq_one :
    sequence.projection.hom.toMonoidHom.comp
        sequence.inclusion.hom.toMonoidHom = 1 := by
  ext g
  rw [MonoidHom.comp_apply]
  have hg : sequence.inclusion g ∈ sequence.inclusion.hom.range :=
    ⟨g, rfl⟩
  rw [sequence.exact] at hg
  exact hg

end ProfiniteFundamentalExactSequence

/--
The canonical exact sequence determined by a surjective profinite-group map.
Its geometric term is definitionally the closed kernel, so no second unrelated
group or exactness certificate can be supplied.
-/
noncomputable def profiniteKernelExactSequence
    {arithmetic galois : ProfiniteGrp.{u}}
    (projection : arithmetic ⟶ galois)
    (surjective : Function.Surjective projection) :
    ProfiniteFundamentalExactSequence
      (closedSubgroupProfiniteGrp
        (profiniteKernelClosedSubgroup projection))
      arithmetic galois where
  inclusion :=
    (closedSubgroupProfiniteInclusion
      (profiniteKernelClosedSubgroup projection)).hom
  projection := projection
  inclusion_injective :=
    (closedSubgroupProfiniteInclusion
      (profiniteKernelClosedSubgroup projection)).injective
  projection_surjective := surjective
  exact := by
    ext element
    constructor
    · rintro ⟨kernelElement, rfl⟩
      exact kernelElement.property
    · intro inKernel
      exact ⟨⟨element, inKernel⟩, rfl⟩

/--
A compatible pair of geometric and arithmetic open immersions between two
fundamental-group exact sequences. This is the group-theoretic square occurring
in IUT I, Definition 3.1(d)-(e).
-/
structure ProfiniteFundamentalGroupInclusion
    (sourceGeometric sourceArithmetic
      targetGeometric targetArithmetic galois : ProfiniteGrp.{u})
    (sourceSequence :
      ProfiniteFundamentalExactSequence
        sourceGeometric sourceArithmetic galois)
    (targetSequence :
      ProfiniteFundamentalExactSequence
        targetGeometric targetArithmetic galois) where
  geometric :
    ProfiniteOpenEmbedding sourceGeometric targetGeometric
  arithmetic :
    ProfiniteOpenEmbedding sourceArithmetic targetArithmetic
  inclusion_square :
    geometric.hom ≫ targetSequence.inclusion =
      sourceSequence.inclusion ≫ arithmetic.hom
  projection_compatible :
    arithmetic.hom ≫ targetSequence.projection =
      sourceSequence.projection

/--
An injective morphism between two fundamental-group exact sequences, allowing
the source and target Galois quotients to differ.

This is the local-to-global decomposition diagram of IUT I, Definition 3.1(e).
-/
structure ProfiniteFundamentalExactSequenceEmbedding
    (sourceGeometric sourceArithmetic sourceGalois
      targetGeometric targetArithmetic targetGalois : ProfiniteGrp.{u})
    (sourceSequence :
      ProfiniteFundamentalExactSequence
        sourceGeometric sourceArithmetic sourceGalois)
    (targetSequence :
      ProfiniteFundamentalExactSequence
        targetGeometric targetArithmetic targetGalois) where
  geometric :
    ProfiniteEmbedding sourceGeometric targetGeometric
  arithmetic :
    ProfiniteEmbedding sourceArithmetic targetArithmetic
  galois :
    ProfiniteEmbedding sourceGalois targetGalois
  inclusion_square :
    geometric.hom ≫ targetSequence.inclusion =
      sourceSequence.inclusion ≫ arithmetic.hom
  projection_square :
    arithmetic.hom ≫ targetSequence.projection =
      sourceSequence.projection ≫ galois.hom

/--
The canonical embedding of the kernel exact sequence of a closed subgroup into
the ambient kernel exact sequence.
-/
noncomputable def profiniteClosedSubgroupExactSequenceEmbedding
    {arithmetic galois : ProfiniteGrp.{u}}
    (subgroup : ClosedSubgroup arithmetic)
    (projection : arithmetic ⟶ galois)
    (projection_surjective : Function.Surjective projection)
    (restricted_surjective :
      Function.Surjective
        (profiniteClosedSubgroupRestriction subgroup projection)) :
    ProfiniteFundamentalExactSequenceEmbedding
      (closedSubgroupProfiniteGrp
        (profiniteKernelClosedSubgroup
          (profiniteClosedSubgroupRestriction subgroup projection)))
      (closedSubgroupProfiniteGrp subgroup)
      galois
      (closedSubgroupProfiniteGrp
        (profiniteKernelClosedSubgroup projection))
      arithmetic
      galois
      (profiniteKernelExactSequence
        (profiniteClosedSubgroupRestriction subgroup projection)
        restricted_surjective)
      (profiniteKernelExactSequence projection projection_surjective) where
  geometric := profiniteRestrictedKernelEmbedding subgroup projection
  arithmetic := closedSubgroupProfiniteInclusion subgroup
  galois :=
    { hom := 𝟙 galois
      injective := Function.injective_id }
  inclusion_square := by
    ext element
    rfl
  projection_square := by
    ext element
    rfl

end Iut
