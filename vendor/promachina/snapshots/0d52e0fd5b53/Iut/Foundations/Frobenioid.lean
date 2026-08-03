/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.Algebra.Category.MonCat.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.Data.PNat.Basic
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Source-shaped Frobenioid foundations

This module begins the formalization of Mochizuki, *The Geometry of
Frobenioids I*, Definitions 1.1-1.3.  In particular, an elementary Frobenioid
is an actual category: an arrow is a base arrow, a zero divisor at its source,
and a positive Frobenius degree, with the composition law of Definition 1.1(iii).

The structures below deliberately expose the remaining hypotheses of the paper.
They do not manufacture a Frobenioid from a natural-number degree preorder.
-/

open CategoryTheory

namespace Iut

universe u

/--
A sharp, integral, saturated commutative additive monoid.

This is the divisorial case of Frobenioids I, Definition 1.1(i).  Saturation is
stated in the Grothendieck group: if a positive multiple of a group element is
represented by the monoid, then the element itself is represented by the
monoid.
-/
structure DivisorialAddMonoid where
  carrier : Type u
  [addCommMonoid : AddCommMonoid carrier]
  integral :
    ∀ a b c : carrier, a + b = a + c -> b = c
  sharp :
    ∀ a : carrier, IsAddUnit a -> a = 0
  saturated :
    ∀ (x : Algebra.GrothendieckAddGroup carrier) (n : ℕ+),
      n.1 • x ∈ Set.range (Algebra.GrothendieckAddGroup.of (M := carrier)) ->
        x ∈ Set.range (Algebra.GrothendieckAddGroup.of (M := carrier))

attribute [instance] DivisorialAddMonoid.addCommMonoid

namespace DivisorialAddMonoid

/-- The bundled additive commutative monoid underlying a divisorial monoid. -/
def toAddCommMonCat (M : DivisorialAddMonoid.{u}) : AddCommMonCat.{u} :=
  AddCommMonCat.of M.carrier

end DivisorialAddMonoid

/--
A contravariant divisorial monoid on a base category.

The injectivity field is Definition 1.1(ii)(a).  The paper's additional
FSM-isomorphism requirement is kept as an explicit predicate parameter because
the formalization does not yet contain the paper's FSM-morphism class.
-/
structure DivisorialMonoidOn
    (D : Type u) [Category.{u} D]
    (IsFSM : ∀ {X Y : D}, (X ⟶ Y) -> Prop) where
  obj : D -> DivisorialAddMonoid.{u}
  pullback :
    ∀ {X Y : D}, (X ⟶ Y) -> (obj Y).carrier →+ (obj X).carrier
  pullback_id :
    ∀ (X : D), pullback (𝟙 X) = AddMonoidHom.id (obj X).carrier
  pullback_comp :
    ∀ {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z),
      pullback (f ≫ g) = (pullback f).comp (pullback g)
  characteristicallyInjective :
    ∀ {X Y : D} (f : X ⟶ Y), Function.Injective (pullback f)
  fsmPullbackIsIso :
    ∀ {X Y : D} (f : X ⟶ Y), IsFSM f -> Function.Bijective (pullback f)

namespace DivisorialMonoidOn

variable {D : Type u} [Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) -> Prop}

/-- The divisor-monoid pseudofunctor, here strictified to an ordinary functor. -/
def functor (Phi : DivisorialMonoidOn D IsFSM) :
    Dᵒᵖ ⥤ AddCommMonCat.{u} where
  obj X := (Phi.obj X.unop).toAddCommMonCat
  map f := AddCommMonCat.ofHom (Phi.pullback f.unop)
  map_id X := by
    ext x
    exact DFunLike.congr_fun (Phi.pullback_id X.unop) x
  map_comp f g := by
    ext x
    exact DFunLike.congr_fun (Phi.pullback_comp g.unop f.unop) x

/-- Pullback extended canonically from a divisorial monoid to its
Grothendieck group.  This is the morphism map of `Phi^gp` in Frobenioids I,
Proposition 4.4(i). -/
noncomputable def gpPullback (Phi : DivisorialMonoidOn D IsFSM)
    {X Y : D} (f : X ⟶ Y) :
    Algebra.GrothendieckAddGroup (Phi.obj Y).carrier →+
      Algebra.GrothendieckAddGroup (Phi.obj X).carrier :=
  Algebra.GrothendieckAddGroup.lift
    (Algebra.GrothendieckAddGroup.of.comp (Phi.pullback f))

@[simp]
theorem gpPullback_of (Phi : DivisorialMonoidOn D IsFSM)
    {X Y : D} (f : X ⟶ Y) (value : (Phi.obj Y).carrier) :
    Phi.gpPullback f (Algebra.GrothendieckAddGroup.of value) =
      Algebra.GrothendieckAddGroup.of (Phi.pullback f value) := by
  let map := Algebra.GrothendieckAddGroup.of.comp (Phi.pullback f)
  change (Algebra.GrothendieckAddGroup.lift map)
      (Algebra.GrothendieckAddGroup.of value) = map value
  change
    ((Algebra.GrothendieckAddGroup.lift map).comp
      Algebra.GrothendieckAddGroup.of) value = map value
  rw [← Algebra.GrothendieckAddGroup.lift_symm_apply]
  exact DFunLike.congr_fun
    (Equiv.symm_apply_apply Algebra.GrothendieckAddGroup.lift map) value

theorem gpPullback_id (Phi : DivisorialMonoidOn D IsFSM) (X : D) :
    Phi.gpPullback (𝟙 X) =
      AddMonoidHom.id
        (Algebra.GrothendieckAddGroup (Phi.obj X).carrier) := by
  apply Algebra.GrothendieckAddGroup.lift.symm.injective
  apply AddMonoidHom.ext
  intro value
  rw [Algebra.GrothendieckAddGroup.lift_symm_apply]
  change Phi.gpPullback (𝟙 X)
      (Algebra.GrothendieckAddGroup.of value) =
    Algebra.GrothendieckAddGroup.of value
  rw [Phi.gpPullback_of, Phi.pullback_id]
  rfl

theorem gpPullback_comp (Phi : DivisorialMonoidOn D IsFSM)
    {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Phi.gpPullback (f ≫ g) =
      (Phi.gpPullback f).comp (Phi.gpPullback g) := by
  apply Algebra.GrothendieckAddGroup.lift.symm.injective
  apply AddMonoidHom.ext
  intro value
  rw [Algebra.GrothendieckAddGroup.lift_symm_apply]
  change Phi.gpPullback (f ≫ g)
      (Algebra.GrothendieckAddGroup.of value) =
    Phi.gpPullback f
      (Phi.gpPullback g (Algebra.GrothendieckAddGroup.of value))
  rw [Phi.gpPullback_of, Phi.gpPullback_of, Phi.gpPullback_of,
    Phi.pullback_comp]
  rfl

end DivisorialMonoidOn

/--
An arrow of the elementary Frobenioid `F_Phi`.

See Frobenioids I, Definition 1.1(iii).
-/
@[ext]
structure ElementaryFrobenioidHom
    {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) -> Prop}
    (Phi : DivisorialMonoidOn D IsFSM)
    (X Y : D) where
  base : X ⟶ Y
  divisor : (Phi.obj X).carrier
  frobeniusDegree : ℕ+

namespace ElementaryFrobenioidHom

variable {D : Type u} [Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) -> Prop}
variable (Phi : DivisorialMonoidOn D IsFSM)

/-- Identity arrow in the elementary Frobenioid. -/
def id (X : D) : ElementaryFrobenioidHom Phi X X where
  base := 𝟙 X
  divisor := 0
  frobeniusDegree := 1

/--
Composition in the elementary Frobenioid:
`(g o f).Div = f^*(g.Div) + deg(g) f.Div`.
-/
def comp {X Y Z : D}
    (f : ElementaryFrobenioidHom Phi X Y)
    (g : ElementaryFrobenioidHom Phi Y Z) :
    ElementaryFrobenioidHom Phi X Z where
  base := f.base ≫ g.base
  divisor :=
    Phi.pullback f.base g.divisor +
      (g.frobeniusDegree.1 : ℕ) • f.divisor
  frobeniusDegree := f.frobeniusDegree * g.frobeniusDegree

@[simp]
theorem id_base (X : D) : (id Phi X).base = 𝟙 X :=
  rfl

@[simp]
theorem id_divisor (X : D) : (id Phi X).divisor = 0 :=
  rfl

@[simp]
theorem id_frobeniusDegree (X : D) :
    (id Phi X).frobeniusDegree = 1 :=
  rfl

@[simp]
theorem comp_base {X Y Z : D}
    (f : ElementaryFrobenioidHom Phi X Y)
    (g : ElementaryFrobenioidHom Phi Y Z) :
    (comp Phi f g).base = f.base ≫ g.base :=
  rfl

@[simp]
theorem comp_divisor {X Y Z : D}
    (f : ElementaryFrobenioidHom Phi X Y)
    (g : ElementaryFrobenioidHom Phi Y Z) :
    (comp Phi f g).divisor =
      Phi.pullback f.base g.divisor +
        (g.frobeniusDegree.1 : ℕ) • f.divisor :=
  rfl

@[simp]
theorem comp_frobeniusDegree {X Y Z : D}
    (f : ElementaryFrobenioidHom Phi X Y)
    (g : ElementaryFrobenioidHom Phi Y Z) :
    (comp Phi f g).frobeniusDegree =
      f.frobeniusDegree * g.frobeniusDegree :=
  rfl

end ElementaryFrobenioidHom

/--
The elementary Frobenioid `F_Phi` of Frobenioids I, Definition 1.1(iii).

Its objects are the objects of the base category.  Its morphisms and composition
are the source definitions, not a preorder surrogate.
-/
def ElementaryFrobenioid
    (D : Type u) [Category.{u} D]
    (IsFSM : ∀ {X Y : D}, (X ⟶ Y) -> Prop)
    (Phi : DivisorialMonoidOn D IsFSM) :=
  let _sourceStructure := Phi
  D

namespace ElementaryFrobenioid

variable {D : Type u} [Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) -> Prop}
variable (Phi : DivisorialMonoidOn D IsFSM)

instance : Category.{u} (ElementaryFrobenioid D IsFSM Phi) where
  Hom X Y := ElementaryFrobenioidHom Phi X Y
  id X := ElementaryFrobenioidHom.id Phi X
  comp f g := ElementaryFrobenioidHom.comp Phi f g
  id_comp f := by
    ext
    · simp
    · simp [ElementaryFrobenioidHom.comp, Phi.pullback_id]
    · simp [ElementaryFrobenioidHom.comp]
  comp_id f := by
    ext
    · simp
    · simp only [ElementaryFrobenioidHom.comp,
        ElementaryFrobenioidHom.id, AddMonoidHom.map_zero, zero_add]
      exact one_nsmul _
    · simp [ElementaryFrobenioidHom.comp]
  assoc f g h := by
    ext
    · simp [Category.assoc]
    · change
        Phi.pullback (f.base ≫ g.base) h.divisor +
            h.frobeniusDegree.1 •
              (Phi.pullback f.base g.divisor +
                g.frobeniusDegree.1 • f.divisor) =
          Phi.pullback f.base
              (Phi.pullback g.base h.divisor +
                h.frobeniusDegree.1 • g.divisor) +
            (g.frobeniusDegree.1 * h.frobeniusDegree.1) • f.divisor
      rw [Phi.pullback_comp]
      simp [nsmul_add, mul_nsmul, add_assoc]
    · simp [ElementaryFrobenioidHom.comp, mul_assoc]

@[simp]
theorem id_divisor (X : ElementaryFrobenioid D IsFSM Phi) :
    (𝟙 X : X ⟶ X).divisor = 0 :=
  rfl

@[simp]
theorem id_frobeniusDegree (X : ElementaryFrobenioid D IsFSM Phi) :
    (𝟙 X : X ⟶ X).frobeniusDegree = 1 :=
  rfl

@[simp]
theorem comp_divisor
    {X Y Z : ElementaryFrobenioid D IsFSM Phi}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).divisor =
      Phi.pullback f.base g.divisor +
        g.frobeniusDegree.1 • f.divisor :=
  rfl

@[simp]
theorem comp_frobeniusDegree
    {X Y Z : ElementaryFrobenioid D IsFSM Phi}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).frobeniusDegree =
      f.frobeniusDegree * g.frobeniusDegree :=
  rfl

/-- The natural projection `F_Phi -> D`. -/
def base : ElementaryFrobenioid D IsFSM Phi ⥤ D where
  obj X := X
  map f := f.base
  map_id _ := rfl
  map_comp _ _ := rfl

end ElementaryFrobenioid

/--
A pre-Frobenioid structure on `C`, in the sense of Frobenioids I,
Definition 1.1(iv).
-/
structure PreFrobenioid
    (C D : Type u) [Category.{u} C] [Category.{u} D]
    (IsFSM : ∀ {X Y : D}, (X ⟶ Y) -> Prop) where
  divisorMonoid : DivisorialMonoidOn D IsFSM
  structureFunctor :
    C ⥤ ElementaryFrobenioid D IsFSM divisorMonoid

namespace PreFrobenioid

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) -> Prop}
variable (P : PreFrobenioid C D IsFSM)

/-- Projection of the pre-Frobenioid to its base category. -/
def base : C ⥤ D :=
  P.structureFunctor ⋙ ElementaryFrobenioid.base P.divisorMonoid

/-- The zero divisor of an arrow of a pre-Frobenioid. -/
def divisor {X Y : C} (f : X ⟶ Y) :
    (P.divisorMonoid.obj ((P.base).obj X)).carrier :=
  (P.structureFunctor.map f).divisor

/-- The positive Frobenius degree of an arrow of a pre-Frobenioid. -/
def frobeniusDegree {X Y : C} (f : X ⟶ Y) : ℕ+ :=
  (P.structureFunctor.map f).frobeniusDegree

/-- Definition 1.2(i): a linear morphism has Frobenius degree one. -/
def IsLinear {X Y : C} (f : X ⟶ Y) : Prop :=
  P.frobeniusDegree f = 1

/-- Definition 1.2(i): an isometric morphism has zero divisor. -/
def IsIsometric {X Y : C} (f : X ⟶ Y) : Prop :=
  P.divisor f = 0

/-- Definition 1.2(ii): a base isomorphism projects to an isomorphism. -/
def IsBaseIso {X Y : C} (f : X ⟶ Y) : Prop :=
  IsIso ((P.base).map f)

/-- Definition 1.2(iii): a pre-step is linear and a base isomorphism. -/
def IsPreStep {X Y : C} (f : X ⟶ Y) : Prop :=
  P.IsLinear f ∧ P.IsBaseIso f

/--
The target of the representable-functor comparison in Definition 1.2(ii).

An element is a morphism to the codomain of `f`, together with a morphism in
the base category to the base of the domain of `f`, satisfying the fiber-product
compatibility equation.
-/
structure PullbackComparisonTarget
    {X Y : C} (f : X ⟶ Y) (T : C) where
  toCodomain : T ⟶ Y
  toBaseDomain : (P.base).obj T ⟶ (P.base).obj X
  commutes :
    (P.base).map toCodomain =
      toBaseDomain ≫ (P.base).map f

/-- The representable-functor comparison map of Definition 1.2(ii). -/
def pullbackComparison
    {X Y : C} (f : X ⟶ Y) (T : C) :
    (T ⟶ X) -> P.PullbackComparisonTarget f T :=
  fun g =>
    { toCodomain := g ≫ f
      toBaseDomain := (P.base).map g
      commutes := by simp }

/--
Definition 1.2(ii): a pullback morphism is one for which the representable
comparison to the indicated fiber product is an isomorphism, expressed here
as a bijection at every test object.
-/
def IsPullback {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ T : C, Function.Bijective (P.pullbackComparison f T)

/-- A base-identity endomorphism in the sense of Definition 1.2(ii). -/
def IsBaseIdentity {X : C} (f : X ⟶ X) : Prop :=
  (P.base).map f = 𝟙 ((P.base).obj X)

/--
Definition 1.2(iii): a co-angular arrow.

The equation is written in Lean's diagrammatic composition order:
`gamma ≫ beta ≫ alpha = f` is the paper's `f = alpha o beta o gamma`.
-/
def IsCoAngular {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ {U V : C}
    (gamma : X ⟶ U) (beta : U ⟶ V) (alpha : V ⟶ Y),
    gamma ≫ beta ≫ alpha = f ->
    P.IsLinear alpha ->
    P.IsPreStep beta ->
    P.IsIsometric beta ->
    (P.IsBaseIso alpha ∨ P.IsBaseIso gamma) ->
    IsIso beta

/-- Definition 1.2(iii): an LB-invertible arrow. -/
def IsLBInvertible {X Y : C} (f : X ⟶ Y) : Prop :=
  P.IsCoAngular f ∧ P.IsIsometric f

/-- Definition 1.2(iii): a morphism of Frobenius type. -/
def IsOfFrobeniusType {X Y : C} (f : X ⟶ Y) : Prop :=
  P.IsLBInvertible f ∧ P.IsBaseIso f

/-- Definition 1.2(iv): an isotropic object. -/
def IsIsotropic (X : C) : Prop :=
  ∀ {Y : C} (f : X ⟶ Y),
    P.IsPreStep f -> P.IsIsometric f -> IsIso f

/--
A Frobenius trivialization of an object, spelling out Definition 1.2(iv).
-/
structure FrobeniusTrivialization (X : C) where
  lift : ℕ+ -> (X ⟶ X)
  map_one : lift 1 = 𝟙 X
  map_mul :
    ∀ m n, lift (m * n) = lift m ≫ lift n
  degree_section :
    ∀ n, P.frobeniusDegree (lift n) = n
  base_identity :
    ∀ n, P.IsBaseIdentity (lift n)
  of_frobenius_type :
    ∀ n, P.IsOfFrobeniusType (lift n)

/-- Definition 1.2(iv): an object admitting a Frobenius trivialization. -/
def IsFrobeniusTrivial (X : C) : Prop :=
  Nonempty (P.FrobeniusTrivialization X)

@[simp]
theorem divisor_id (X : C) : P.divisor (𝟙 X) = 0 := by
  change (P.structureFunctor.map (𝟙 X)).divisor = 0
  rw [P.structureFunctor.map_id]
  rfl

@[simp]
theorem frobeniusDegree_id (X : C) :
    P.frobeniusDegree (𝟙 X) = 1 := by
  simp [frobeniusDegree]

theorem divisor_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P.divisor (f ≫ g) =
      P.divisorMonoid.pullback ((P.base).map f) (P.divisor g) +
        (P.frobeniusDegree g).1 • P.divisor f := by
  change
    (P.structureFunctor.map (f ≫ g)).divisor =
      P.divisorMonoid.pullback (P.structureFunctor.map f).base
          (P.structureFunctor.map g).divisor +
        (P.structureFunctor.map g).frobeniusDegree.1 •
          (P.structureFunctor.map f).divisor
  rw [P.structureFunctor.map_comp]
  rfl

theorem frobeniusDegree_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P.frobeniusDegree (f ≫ g) =
      P.frobeniusDegree f * P.frobeniusDegree g := by
  change
    (P.structureFunctor.map (f ≫ g)).frobeniusDegree =
      (P.structureFunctor.map f).frobeniusDegree *
        (P.structureFunctor.map g).frobeniusDegree
  rw [P.structureFunctor.map_comp]
  rfl

/-- The morphism property cutting out the paper's wide subcategory of isometries. -/
def isometricMorphismProperty : MorphismProperty C :=
  fun _ _ map => P.IsIsometric map

instance isometricMorphismProperty_isMultiplicative :
    P.isometricMorphismProperty.IsMultiplicative where
  id_mem X := P.divisor_id X
  comp_mem f g hf hg := by
    change P.divisor (f ≫ g) = 0
    rw [P.divisor_comp, hf, hg]
    simp

/-- The wide subcategory with all objects and precisely the isometric arrows. -/
abbrev IsometryCategory :=
  WideSubcategory P.isometricMorphismProperty

/-- The faithful inclusion of the isometry subcategory into the Frobenioid carrier. -/
def isometryCategoryInclusion : P.IsometryCategory ⥤ C :=
  wideSubcategoryInclusion P.isometricMorphismProperty

/-- An object of the slice of `C` over `A`. -/
structure PullbackSliceObject (A : C) where
  source : C
  hom : source ⟶ A

/-- A morphism in the slice of `C` over `A`. -/
structure PullbackSliceHom {A : C}
    (X Y : PullbackSliceObject A) where
  hom : X.source ⟶ Y.source
  commutes : hom ≫ Y.hom = X.hom

/-- An object of the base-category slice over the base of `A`. -/
structure BaseSliceObject (A : C) where
  source : D
  hom : source ⟶ (P.base).obj A

/-- A morphism in the base-category slice over the base of `A`. -/
structure BaseSliceHom {A : C}
    (X Y : P.BaseSliceObject A) where
  hom : X.source ⟶ Y.source
  commutes : hom ≫ Y.hom = X.hom

/-- Projection of a carrier slice object to the base-category slice. -/
def PullbackSliceObject.toBase {A : C}
    (X : PullbackSliceObject A) : P.BaseSliceObject A where
  source := (P.base).obj X.source
  hom := (P.base).map X.hom

/-- Projection of a carrier slice morphism to the base-category slice. -/
def PullbackSliceHom.toBase {A : C}
    {X Y : PullbackSliceObject A}
    (f : PullbackSliceHom X Y) :
    P.BaseSliceHom (X.toBase P) (Y.toBase P) where
  hom := (P.base).map f.hom
  commutes := by
    change
      (P.base).map f.hom ≫ (P.base).map Y.hom =
        (P.base).map X.hom
    rw [← (P.base).map_comp, f.commutes]

/-- An isomorphism of base-category slice objects. -/
structure BaseSliceIso {A : C}
    (X Y : P.BaseSliceObject A) where
  iso : X.source ≅ Y.source
  hom_commutes : iso.hom ≫ Y.hom = X.hom

/--
Definition 1.3(i)(c), stated without hiding the slice categories behind an
opaque proposition.
-/
structure PullbackBaseSliceEquivalence (A : C) where
  essentiallySurjective :
    ∀ Y : P.BaseSliceObject A,
      ∃ X : PullbackSliceObject A,
        P.IsPullback X.hom ∧
          Nonempty (P.BaseSliceIso (X.toBase P) Y)
  fullyFaithful :
    ∀ (X Y : PullbackSliceObject A),
      P.IsPullback X.hom ->
      P.IsPullback Y.hom ->
      Function.Bijective
        (fun f : PullbackSliceHom X Y =>
          PullbackSliceHom.toBase P f)

/-- The common-pre-step witness in Definition 1.3(i)(b). -/
structure CommonPreStepWitness
    (A B : C) (e : (P.base).obj A ≅ (P.base).obj B) where
  midpoint : C
  toLeft : midpoint ⟶ A
  toRight : midpoint ⟶ B
  toLeft_preStep : P.IsPreStep toLeft
  toRight_preStep : P.IsPreStep toRight
  leftBaseInverse : (P.base).obj A ⟶ (P.base).obj midpoint
  leftBaseInverse_hom :
    leftBaseInverse ≫ (P.base).map toLeft =
      𝟙 ((P.base).obj A)
  hom_leftBaseInverse :
    (P.base).map toLeft ≫ leftBaseInverse =
      𝟙 ((P.base).obj midpoint)
  comparison :
    leftBaseInverse ≫ (P.base).map toRight = e.hom

/-- The existence and essential uniqueness clause of Definition 1.3(ii). -/
structure FrobeniusDegreeWitness (A : C) (n : ℕ+) where
  codomain : C
  hom : A ⟶ codomain
  ofFrobeniusType : P.IsOfFrobeniusType hom
  degree : P.frobeniusDegree hom = n
  essentiallyUnique :
    ∀ {B : C} (f : A ⟶ B),
      P.IsOfFrobeniusType f ->
      P.frobeniusDegree f = n ->
      ∃! e : codomain ≅ B, hom ≫ e.hom = f

/-- A factorization from Definition 1.3(iv)(a). -/
structure FrobenioidFactorization {X Y : C} (f : X ⟶ Y) where
  frobeniusCodomain : C
  preStepCodomain : C
  frobenius : X ⟶ frobeniusCodomain
  preStep : frobeniusCodomain ⟶ preStepCodomain
  pullback : preStepCodomain ⟶ Y
  frobenius_type : P.IsOfFrobeniusType frobenius
  preStep_type : P.IsPreStep preStep
  pullback_type : P.IsPullback pullback
  composite : frobenius ≫ preStep ≫ pullback = f

/-- An isomorphism between two Definition 1.3(iv)(a) factorizations. -/
structure FrobenioidFactorizationIso
    {X Y : C} {f : X ⟶ Y}
    (left right : P.FrobenioidFactorization f) where
  frobeniusCodomainIso :
    left.frobeniusCodomain ≅ right.frobeniusCodomain
  preStepCodomainIso :
    left.preStepCodomain ≅ right.preStepCodomain
  frobenius_square :
    left.frobenius ≫ frobeniusCodomainIso.hom =
      right.frobenius
  preStep_square :
    frobeniusCodomainIso.inv ≫ left.preStep ≫
        preStepCodomainIso.hom =
      right.preStep
  pullback_square :
    preStepCodomainIso.inv ≫ left.pullback =
      right.pullback

/-- A co-angular/isometric factorization of a pre-step. -/
structure PreStepFactorization
    {X Y : C} (f : X ⟶ Y) (coAngularFirst : Bool) where
  midpoint : C
  first : X ⟶ midpoint
  second : midpoint ⟶ Y
  first_preStep : P.IsPreStep first
  second_preStep : P.IsPreStep second
  first_kind :
    if coAngularFirst then P.IsCoAngular first else P.IsIsometric first
  second_kind :
    if coAngularFirst then P.IsIsometric second else P.IsCoAngular second
  composite : first ≫ second = f

/-- An isomorphism between two pre-step factorizations of the same kind. -/
structure PreStepFactorizationIso
    {X Y : C} {f : X ⟶ Y} {coAngularFirst : Bool}
    (left right : P.PreStepFactorization f coAngularFirst) where
  midpointIso : left.midpoint ≅ right.midpoint
  first_square :
    left.first ≫ midpointIso.hom = right.first
  second_square :
    midpointIso.inv ≫ left.second = right.second

/-- A base-identity linear endomorphism, i.e. an element of `O^bullet(A)`. -/
@[ext]
structure LinearBaseIdentityEndomorphism (A : C) where
  hom : A ⟶ A
  linear : P.IsLinear hom
  baseIdentity : P.IsBaseIdentity hom

instance (A : C) : Monoid (P.LinearBaseIdentityEndomorphism A) where
  one :=
    { hom := 𝟙 A
      linear := P.frobeniusDegree_id A
      baseIdentity := by simp [IsBaseIdentity] }
  mul left right :=
    { hom := left.hom ≫ right.hom
      linear := by
        rw [IsLinear, P.frobeniusDegree_comp,
          left.linear, right.linear]
        simp
      baseIdentity := by
        rw [IsBaseIdentity, (P.base).map_comp,
          left.baseIdentity, right.baseIdentity]
        simp }
  one_mul a := by
    apply LinearBaseIdentityEndomorphism.ext
    change 𝟙 A ≫ a.hom = a.hom
    simp
  mul_one a := by
    apply LinearBaseIdentityEndomorphism.ext
    change a.hom ≫ 𝟙 A = a.hom
    simp
  mul_assoc a b c := by
    apply LinearBaseIdentityEndomorphism.ext
    change
      (a.hom ≫ b.hom) ≫ c.hom =
        a.hom ≫ b.hom ≫ c.hom
    simp [Category.assoc]

/-- A base-identity automorphism, i.e. an element of `O^x(A)`. -/
structure BaseIdentityAutomorphism (A : C) where
  iso : A ≅ A
  baseIdentity : P.IsBaseIdentity iso.hom

/--
The unit/endomorphism transport along a co-angular pre-step in Definition
1.3(iii)(c).
-/
structure CoAngularUnitTransport
    {A B : C} (f : A ⟶ B) where
  transport :
    P.LinearBaseIdentityEndomorphism A ≃*
      P.LinearBaseIdentityEndomorphism B
  conjugates :
    ∀ alpha,
      alpha.hom ≫ f = f ≫ (transport alpha).hom

/-- The divisibility preorder on the divisor monoid at an object. -/
abbrev DivisorOrder (A : C) :=
  (P.divisorMonoid.obj ((P.base).obj A)).carrier

instance (A : C) : Preorder (P.DivisorOrder A) where
  le left right := ∃ remainder, right = left + remainder
  le_refl value := ⟨0, by simp⟩
  le_trans left middle right hleft hright := by
    rcases hleft with ⟨first, rfl⟩
    rcases hright with ⟨second, rfl⟩
    exact ⟨first + second, by simp [add_assoc]⟩

/-- An outgoing co-angular pre-step with a prescribed zero divisor. -/
structure OutgoingCoAngularPreStep
    (A : C) (Z : P.DivisorOrder A) where
  target : C
  hom : A ⟶ target
  preStep : P.IsPreStep hom
  coAngular : P.IsCoAngular hom
  divisor_eq : P.divisor hom = Z

/--
An incoming co-angular pre-step whose divisor, transported to the fixed
codomain, is `Z`.
-/
structure IncomingCoAngularPreStep
    (A : C) (Z : P.DivisorOrder A) where
  source : C
  hom : source ⟶ A
  preStep : P.IsPreStep hom
  coAngular : P.IsCoAngular hom
  pulledBack_divisor_eq :
    P.divisorMonoid.pullback ((P.base).map hom) Z =
      P.divisor hom

/-- An isotropic hull with its source universal property. -/
structure IsotropicHull (A : C) where
  hull : C
  hom : A ⟶ hull
  preStep : P.IsPreStep hom
  isometric : P.IsIsometric hom
  isotropic : P.IsIsotropic hull
  lift :
    ∀ {B : C} (f : A ⟶ B), P.IsIsotropic B ->
      ∃! g : hull ⟶ B, hom ≫ g = f

/--
The seven axiom groups of Frobenioids I, Definition 1.3.

Every field is a source formula with its existence or uniqueness content
visible.  In particular, the two divisor-order equivalences are expressed by
essential representatives and unique slice morphisms, and the factorization
clauses expose their unique comparison isomorphisms.
-/
structure FrobenioidAxioms where
  baseRepresented :
    ∀ B : D,
      ∃ A : C,
        P.IsFrobeniusTrivial A ∧
          Nonempty ((P.base).obj A ≅ B)
  commonPreSteps :
    ∀ (A B : C) (e : (P.base).obj A ≅ (P.base).obj B),
      Nonempty (P.CommonPreStepWitness A B e)
  pullbackBaseSlices :
    ∀ A : C, P.PullbackBaseSliceEquivalence A
  frobeniusDegree :
    ∀ (A : C) (n : ℕ+), P.FrobeniusDegreeWitness A n
  coAngular_comp :
    ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
      P.IsCoAngular f -> P.IsCoAngular g ->
        P.IsCoAngular (f ≫ g)
  coAngular_parallelToCoAngularPreStep :
    ∀ {X Y : C} (f g : X ⟶ Y),
      P.IsPreStep f -> P.IsCoAngular f -> P.IsCoAngular g
  unitTransport :
    ∀ {A B : C} (f : A ⟶ B),
      P.IsPreStep f -> P.IsCoAngular f ->
        P.CoAngularUnitTransport f
  unitTransport_unique :
    ∀ {A B : C} (f : A ⟶ B)
      (_hfPreStep : P.IsPreStep f)
      (_hfCoAngular : P.IsCoAngular f)
      (left right : P.CoAngularUnitTransport f),
      left = right
  unitTransport_dependsOnlyOnBase :
    ∀ {A B : C} (f g : A ⟶ B)
      (hfPreStep : P.IsPreStep f)
      (hfCoAngular : P.IsCoAngular f)
      (hgPreStep : P.IsPreStep g)
      (hgCoAngular : P.IsCoAngular g),
      (P.base).map f = (P.base).map g ->
        (unitTransport f hfPreStep hfCoAngular).transport =
          (unitTransport g hgPreStep hgCoAngular).transport
  outgoingDivisorRepresentative :
    ∀ (A : C) (Z : P.DivisorOrder A),
      P.OutgoingCoAngularPreStep A Z
  outgoingDivisorOrderFullyFaithful :
    ∀ {A : C} {leftDivisor rightDivisor : P.DivisorOrder A}
      (left : P.OutgoingCoAngularPreStep A leftDivisor)
      (right : P.OutgoingCoAngularPreStep A rightDivisor),
      leftDivisor ≤ rightDivisor ↔
        ∃! f : left.target ⟶ right.target,
          left.hom ≫ f = right.hom
  outgoingDivisorRepresentative_unique :
    ∀ {A : C} {Z : P.DivisorOrder A}
      (left right : P.OutgoingCoAngularPreStep A Z),
      ∃! e : left.target ≅ right.target,
        left.hom ≫ e.hom = right.hom
  incomingDivisor :
    ∀ {A B : C} (f : B ⟶ A),
      P.IsPreStep f -> P.IsCoAngular f ->
        ∃! Z : P.DivisorOrder A,
          P.divisorMonoid.pullback ((P.base).map f) Z =
            P.divisor f
  incomingDivisorRepresentative :
    ∀ (A : C) (Z : P.DivisorOrder A),
      P.IncomingCoAngularPreStep A Z
  incomingDivisorOrderFullyFaithful :
    ∀ {A : C} {leftDivisor rightDivisor : P.DivisorOrder A}
      (left : P.IncomingCoAngularPreStep A leftDivisor)
      (right : P.IncomingCoAngularPreStep A rightDivisor),
      rightDivisor ≤ leftDivisor ↔
        ∃! f : left.source ⟶ right.source,
          f ≫ right.hom = left.hom
  incomingDivisorRepresentative_unique :
    ∀ {A : C} {Z : P.DivisorOrder A}
      (left right : P.IncomingCoAngularPreStep A Z),
      ∃! e : left.source ≅ right.source,
        e.hom ≫ right.hom = left.hom
  factorization :
    ∀ {X Y : C} (f : X ⟶ Y),
      Nonempty (P.FrobenioidFactorization f)
  pullback_linear_lbInvertible :
    ∀ {X Y : C} (f : X ⟶ Y),
      P.IsPullback f -> P.IsLinear f ∧ P.IsLBInvertible f
  factorizationIso :
    ∀ {X Y : C} {f : X ⟶ Y}
      (left right : P.FrobenioidFactorization f),
      P.FrobenioidFactorizationIso left right
  factorizationIso_unique :
    ∀ {X Y : C} {f : X ⟶ Y}
      (left right : P.FrobenioidFactorization f)
      (first second : P.FrobenioidFactorizationIso left right),
      first = second
  preStep_mono :
    ∀ {X Y : C} (f : X ⟶ Y), P.IsPreStep f -> Mono f
  preStep_coAngularThenIsometric :
    ∀ {X Y : C} (f : X ⟶ Y), P.IsPreStep f ->
      Nonempty (P.PreStepFactorization f true)
  preStep_isometricThenCoAngular :
    ∀ {X Y : C} (f : X ⟶ Y), P.IsPreStep f ->
      Nonempty (P.PreStepFactorization f false)
  preStepFactorizationIso :
    ∀ {X Y : C} {f : X ⟶ Y} {coAngularFirst : Bool}
      (left right : P.PreStepFactorization f coAngularFirst),
      P.PreStepFactorizationIso left right
  preStepFactorizationIso_unique :
    ∀ {X Y : C} {f : X ⟶ Y} {coAngularFirst : Bool}
      (left right : P.PreStepFactorization f coAngularFirst)
      (first second : P.PreStepFactorizationIso left right),
      first = second
  faithfulUpToUnits :
    ∀ {A B : C} (f g : A ⟶ B),
      (P.base).map f = (P.base).map g ->
      P.divisor f = P.divisor g ->
      P.IsPreStep f -> P.IsCoAngular f ->
      P.IsPreStep g -> P.IsCoAngular g ->
      ∃! alpha : P.BaseIdentityAutomorphism B,
        g ≫ alpha.iso.hom = f
  isotropicHull :
    ∀ A : C, Nonempty (P.IsotropicHull A)
  isotropic_closedUnderTargets :
    ∀ {A B : C} (_f : A ⟶ B),
      P.IsIsotropic A -> P.IsIsotropic B

end PreFrobenioid

/--
A packaged pre-Frobenioid with the connectedness and total-epimorphicity
hypotheses of Frobenioids I, Definition 1.1(iv).

This is still a *pre*-Frobenioid presentation: the seven axiom groups of
Definition 1.3 are deliberately not fields of this record yet.
-/
structure PreFrobenioidPresentation where
  carrier : CategoryTheory.Cat.{u, u}
  baseCategory : CategoryTheory.Cat.{u, u}
  isFSM :
    ∀ {X Y : baseCategory}, (X ⟶ Y) -> Prop
  preFrobenioid :
    PreFrobenioid carrier baseCategory isFSM
  carrierConnected : CategoryTheory.IsConnected carrier
  baseConnected : CategoryTheory.IsConnected baseCategory
  carrierTotallyEpimorphic :
    ∀ {X Y : carrier} (f : X ⟶ Y), Epi f
  baseTotallyEpimorphic :
    ∀ {X Y : baseCategory} (f : X ⟶ Y), Epi f

/--
A packaged Frobenioid: the Definition 1.1 pre-Frobenioid data, connected and
totally epimorphic category hypotheses, and every axiom of Definition 1.3.
-/
structure FrobenioidPresentation extends PreFrobenioidPresentation.{u} where
  axioms : preFrobenioid.FrobenioidAxioms

namespace PreFrobenioid

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) -> Prop}
variable (P : PreFrobenioid C D IsFSM)

/--
An object of the isotropic subcategory `C^istr` of Frobenioids I,
Proposition 2.2.
-/
structure IsotropicLinearObject where
  obj : C
  isotropic : P.IsIsotropic obj

/--
A linear arrow between isotropic objects.  These are the arrows of
`(C^istr)^lin` in Frobenioids I, Proposition 2.2 and Definition 2.3.
-/
@[ext]
structure IsotropicLinearHom
    (X Y : P.IsotropicLinearObject) where
  hom : X.obj ⟶ Y.obj
  linear : P.IsLinear hom

instance : Category.{u} P.IsotropicLinearObject where
  Hom := P.IsotropicLinearHom
  id X :=
    { hom := 𝟙 X.obj
      linear := P.frobeniusDegree_id X.obj }
  comp f g :=
    { hom := f.hom ≫ g.hom
      linear := by
        rw [IsLinear, P.frobeniusDegree_comp, f.linear, g.linear]
        simp }
  id_comp f := by
    ext
    simp
  comp_id f := by
    ext
    simp
  assoc f g h := by
    ext
    simp [Category.assoc]

@[simp]
theorem isotropicLinear_id_hom (X : P.IsotropicLinearObject) :
    (𝟙 X : X ⟶ X).hom = 𝟙 X.obj :=
  rfl

@[simp]
theorem isotropicLinear_comp_hom
    {X Y Z : P.IsotropicLinearObject}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

/--
The source content of Frobenioids I, Proposition 2.2(ii),(iv), needed by
Definition 2.3.

The object monoids are the actual base-identity linear endomorphisms
`O^triangle(A)`.  `pullback` supplies the unique contravariant transport on
linear arrows between isotropic objects, while `hullInclusion` is the natural
injection associated to an isotropic hull.  Constructing this record from the
Definition 1.3 axioms is Proposition 2.2 and remains a theorem obligation; it
is not a field of `FrobenioidPresentation`.
-/
structure RationalMonoidTransport where
  pullback :
    ∀ {X Y : P.IsotropicLinearObject}, (X ⟶ Y) ->
      P.LinearBaseIdentityEndomorphism Y.obj →*
        P.LinearBaseIdentityEndomorphism X.obj
  pullback_id :
    ∀ X,
      pullback (𝟙 X) =
        MonoidHom.id (P.LinearBaseIdentityEndomorphism X.obj)
  pullback_comp :
    ∀ {X Y Z : P.IsotropicLinearObject}
      (f : X ⟶ Y) (g : Y ⟶ Z),
      pullback (f ≫ g) =
        (pullback f).comp (pullback g)
  hullInclusion :
    ∀ (A : C) (hull : P.IsotropicHull A),
      P.LinearBaseIdentityEndomorphism A →*
        P.LinearBaseIdentityEndomorphism hull.hull
  hullInclusion_injective :
    ∀ (A : C) (hull : P.IsotropicHull A),
      Function.Injective (hullInclusion A hull)

namespace RationalMonoidTransport

variable {P : PreFrobenioid C D IsFSM}

/-- Proposition 2.2(ii), packaged as the literal contravariant functor. -/
def functor (R : P.RationalMonoidTransport) :
    P.IsotropicLinearObjectᵒᵖ ⥤ MonCat.{u} where
  obj X :=
    MonCat.of
      (P.LinearBaseIdentityEndomorphism X.unop.obj)
  map f := MonCat.ofHom (R.pullback f.unop)
  map_id X := by
    apply MonCat.hom_ext
    simpa using R.pullback_id X.unop
  map_comp f g := by
    apply MonCat.hom_ext
    simpa using R.pullback_comp g.unop f.unop

end RationalMonoidTransport

/--
A characteristic splitting in the exact sense of Frobenioids I,
Definition 2.3.

The selected submonoids form a subfunctor of `O^triangle(-)`.  Objectwise,
multiplication by units is bijective and the two factors commute, which is the
paper's functorial monoid splitting
`O^times(A) x tau(A) ~= O^triangle(A)`.  The final clause is Definition
2.3(b), expressed using the Proposition 2.2(iv) isotropic-hull injection.
-/
structure CharacteristicSplitting
    (R : P.RationalMonoidTransport) where
  tau :
    ∀ X : P.IsotropicLinearObject,
      Submonoid (P.LinearBaseIdentityEndomorphism X.obj)
  pullback_mem :
    ∀ {X Y : P.IsotropicLinearObject}
      (f : X ⟶ Y)
      (value : P.LinearBaseIdentityEndomorphism Y.obj),
      value ∈ tau Y ->
        R.pullback f value ∈ tau X
  units_commute :
    ∀ (X : P.IsotropicLinearObject)
      (unit :
        Units (P.LinearBaseIdentityEndomorphism X.obj))
      (characteristic : tau X),
      Commute
        (unit : P.LinearBaseIdentityEndomorphism X.obj)
        characteristic.1
  multiplication_bijective :
    ∀ X : P.IsotropicLinearObject,
      Function.Bijective
        (fun pair :
            Units (P.LinearBaseIdentityEndomorphism X.obj) ×
              tau X =>
          (pair.1 :
              P.LinearBaseIdentityEndomorphism X.obj) *
            pair.2.1)
  isotropicHull_mem_range :
    ∀ (A : C) (hull : P.IsotropicHull A)
      (characteristic :
        tau
          { obj := hull.hull
            isotropic := hull.isotropic }),
      characteristic.1 ∈ Set.range (R.hullInclusion A hull)

end PreFrobenioid

/--
A split Frobenioid as used in IUT I, Examples 3.2-3.4 and Definition 5.2(ii):
a Frobenioid together with a nonempty collection of Definition 2.3
characteristic splittings.

The Proposition 2.2 transport is stored separately from the splitting choices
so that the source reconstruction theorem remains visible.
-/
structure SplitFrobenioidPresentation where
  frobenioid : FrobenioidPresentation.{u}
  rationalMonoids :
    frobenioid.preFrobenioid.RationalMonoidTransport
  splittingIndex : Type u
  splittingIndex_nonempty : Nonempty splittingIndex
  splitting :
    splittingIndex ->
      frobenioid.preFrobenioid.CharacteristicSplitting rationalMonoids

/--
An equivalence of split Frobenioids.

Besides an equivalence of the underlying categories, this records the
transport that is relevant to Frobenioids I, Definition 2.3: linear arrows and
isotropic objects are preserved, the actual rational-function endomorphism
monoids are naturally equivalent, and the indexed characteristic-splitting
submonoids correspond.  This is strictly stronger than an equivalence between
bare carrier categories.
-/
structure SplitFrobenioidEquivalence
    (source target : SplitFrobenioidPresentation.{u}) where
  carrier :
    CategoryTheory.Equivalence
      source.frobenioid.carrier
      target.frobenioid.carrier
  map_isotropic :
    ∀ X :
      source.frobenioid.preFrobenioid.IsotropicLinearObject,
      target.frobenioid.preFrobenioid.IsIsotropic
        (carrier.functor.obj X.obj)
  map_linear :
    ∀ {X Y :
        source.frobenioid.preFrobenioid.IsotropicLinearObject}
      (f : X ⟶ Y),
      target.frobenioid.preFrobenioid.IsLinear
        (carrier.functor.map f.hom)
  rationalMonoidIso :
    ∀ X :
      source.frobenioid.preFrobenioid.IsotropicLinearObject,
      source.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
          X.obj ≃*
        target.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
          (carrier.functor.obj X.obj)
  rationalMonoidIso_hom :
    ∀ (X :
        source.frobenioid.preFrobenioid.IsotropicLinearObject)
      (value :
        source.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
          X.obj),
      (rationalMonoidIso X value).hom =
        carrier.functor.map value.hom
  pullback_compatible :
    ∀ {X Y :
        source.frobenioid.preFrobenioid.IsotropicLinearObject}
      (f : X ⟶ Y)
      (value :
        source.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
          Y.obj),
      target.rationalMonoids.pullback
          (X :=
            { obj := carrier.functor.obj X.obj
              isotropic := map_isotropic X })
          (Y :=
            { obj := carrier.functor.obj Y.obj
              isotropic := map_isotropic Y })
          { hom := carrier.functor.map f.hom
            linear := map_linear f }
          (rationalMonoidIso Y value) =
        rationalMonoidIso X
          (source.rationalMonoids.pullback f value)
  splittingIndexEquiv :
    source.splittingIndex ≃ target.splittingIndex
  splitting_compatible :
    ∀ (index : source.splittingIndex)
      (X :
        source.frobenioid.preFrobenioid.IsotropicLinearObject)
      (value :
        source.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
          X.obj),
      value ∈ (source.splitting index).tau X ↔
        rationalMonoidIso X value ∈
          (target.splitting (splittingIndexEquiv index)).tau
            { obj := carrier.functor.obj X.obj
              isotropic := map_isotropic X }

namespace SplitFrobenioidEquivalence

variable
    {source middle target : SplitFrobenioidPresentation.{u}}

/-- Identity equivalence of a split Frobenioid. -/
def refl (source : SplitFrobenioidPresentation.{u}) :
    SplitFrobenioidEquivalence source source where
  carrier := CategoryTheory.Equivalence.refl
  map_isotropic X := X.isotropic
  map_linear f := f.linear
  rationalMonoidIso _ := MulEquiv.refl _
  rationalMonoidIso_hom _ _ := rfl
  pullback_compatible _ _ := rfl
  splittingIndexEquiv := Equiv.refl _
  splitting_compatible _ _ _ := Iff.rfl

/-- Composition of structure-preserving split-Frobenioid equivalences. -/
def trans
    (first : SplitFrobenioidEquivalence source middle)
    (second : SplitFrobenioidEquivalence middle target) :
    SplitFrobenioidEquivalence source target where
  carrier := first.carrier.trans second.carrier
  map_isotropic X :=
    second.map_isotropic
      { obj := first.carrier.functor.obj X.obj
        isotropic := first.map_isotropic X }
  map_linear {X Y} f := by
    change
      target.frobenioid.preFrobenioid.IsLinear
        (second.carrier.functor.map
          (first.carrier.functor.map f.hom))
    exact
      second.map_linear
        (X :=
          { obj := first.carrier.functor.obj X.obj
            isotropic := first.map_isotropic X })
        (Y :=
          { obj := first.carrier.functor.obj Y.obj
            isotropic := first.map_isotropic Y })
        { hom := first.carrier.functor.map f.hom
          linear := first.map_linear f }
  rationalMonoidIso X :=
    (first.rationalMonoidIso X).trans
      (second.rationalMonoidIso
        { obj := first.carrier.functor.obj X.obj
          isotropic := first.map_isotropic X })
  rationalMonoidIso_hom X value := by
    change
      (second.rationalMonoidIso
          { obj := first.carrier.functor.obj X.obj
            isotropic := first.map_isotropic X }
          (first.rationalMonoidIso X value)).hom =
        second.carrier.functor.map
          (first.carrier.functor.map value.hom)
    rw [second.rationalMonoidIso_hom]
    rw [first.rationalMonoidIso_hom]
  pullback_compatible {X Y} f value := by
    change
      target.rationalMonoids.pullback
          (X :=
            { obj :=
                second.carrier.functor.obj
                  (first.carrier.functor.obj X.obj)
              isotropic :=
                second.map_isotropic
                  { obj := first.carrier.functor.obj X.obj
                    isotropic := first.map_isotropic X } })
          (Y :=
            { obj :=
                second.carrier.functor.obj
                  (first.carrier.functor.obj Y.obj)
              isotropic :=
                second.map_isotropic
                  { obj := first.carrier.functor.obj Y.obj
                    isotropic := first.map_isotropic Y } })
          { hom :=
              second.carrier.functor.map
                (first.carrier.functor.map f.hom)
            linear :=
              second.map_linear
                (X :=
                  { obj := first.carrier.functor.obj X.obj
                    isotropic := first.map_isotropic X })
                (Y :=
                  { obj := first.carrier.functor.obj Y.obj
                    isotropic := first.map_isotropic Y })
                { hom := first.carrier.functor.map f.hom
                  linear := first.map_linear f } }
          (second.rationalMonoidIso
            { obj := first.carrier.functor.obj Y.obj
              isotropic := first.map_isotropic Y }
            (first.rationalMonoidIso Y value)) =
        second.rationalMonoidIso
          { obj := first.carrier.functor.obj X.obj
            isotropic := first.map_isotropic X }
          (first.rationalMonoidIso X
            (source.rationalMonoids.pullback f value))
    have hsecond :=
      second.pullback_compatible
        (X :=
          { obj := first.carrier.functor.obj X.obj
            isotropic := first.map_isotropic X })
        (Y :=
          { obj := first.carrier.functor.obj Y.obj
            isotropic := first.map_isotropic Y })
        (f :=
          { hom := first.carrier.functor.map f.hom
            linear := first.map_linear f })
        (value := first.rationalMonoidIso Y value)
    rw [first.pullback_compatible] at hsecond
    exact hsecond
  splittingIndexEquiv :=
    first.splittingIndexEquiv.trans
      second.splittingIndexEquiv
  splitting_compatible index X value := by
    rw [first.splitting_compatible]
    exact
      second.splitting_compatible
        (first.splittingIndexEquiv index)
        { obj := first.carrier.functor.obj X.obj
          isotropic := first.map_isotropic X }
        (first.rationalMonoidIso X value)

end SplitFrobenioidEquivalence

end Iut
