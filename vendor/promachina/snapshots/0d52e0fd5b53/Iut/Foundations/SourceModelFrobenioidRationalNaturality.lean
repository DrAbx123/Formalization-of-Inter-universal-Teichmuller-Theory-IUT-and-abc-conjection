/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceModelFrobenioidColimitAxioms

/-!
# Naturality of rational functions in the model Frobenioid

Frobenioids I, Theorem 5.2(ii) identifies the rational-function functor
`O^times(-)` associated to the birationalization of the model Frobenioid with
the input group-like monoid `B`.  This file constructs the Proposition 2.2
transport on the actual filtered Hom-colimit, restricts it along the canonical
zero-object section over `D`, and proves the asserted natural isomorphism and
its compatibility with `DivB`.
-/

open CategoryTheory

namespace Iut.SourceModelFrobenioid.Carrier.ColimitBirationalObject

universe u

noncomputable section

variable {D : Type u} [categoryD : Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM} {data : Input Phi}

private abbrev P := preFrobenioid (Phi := Phi) (data := data)

/-- Pullback of a linear base-identity endomorphism along a linear colimit
arrow, expressed through its rational-function coordinate. -/
def linearEndomorphismPullback
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (_linear : P.IsLinear arrow)
    (alpha : P.LinearBaseIdentityEndomorphism target) :
    P.LinearBaseIdentityEndomorphism source :=
  (rationalFunctionEquiv (Phi := Phi) (data := data) source).symm
    (Multiplicative.ofAdd
      (data.rationalFunctions.pullback (P.base.map arrow)
        (rationalFunctionEquiv (Phi := Phi) (data := data) target alpha).toAdd))

/-- The pullback operation is multiplicative. -/
def linearEndomorphismPullbackHom
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (_linear : P.IsLinear arrow) :
    P.LinearBaseIdentityEndomorphism target →*
      P.LinearBaseIdentityEndomorphism source :=
  (rationalFunctionEquiv (Phi := Phi) (data := data) source).symm.toMonoidHom.comp
    ((data.rationalFunctions.pullback (P.base.map arrow)).toMultiplicative.comp
      (rationalFunctionEquiv (Phi := Phi) (data := data) target).toMonoidHom)

@[simp]
theorem linearEndomorphismPullbackHom_apply
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (linear : P.IsLinear arrow)
    (alpha : P.LinearBaseIdentityEndomorphism target) :
    linearEndomorphismPullbackHom arrow linear alpha =
      linearEndomorphismPullback arrow linear alpha :=
  rfl

/-- Pullback is characterized by the conjugation square of Proposition
2.2(ii). -/
theorem linearEndomorphismPullback_conjugates
    {source target : ColimitBirationalObject (Phi := Phi) (data := data)}
    (arrow : source ⟶ target) (linear : P.IsLinear arrow)
    (alpha : P.LinearBaseIdentityEndomorphism target) :
    (linearEndomorphismPullback arrow linear alpha).hom ≫ arrow =
      arrow ≫ alpha.hom := by
  let comparison := comparisonFunctor (Phi := Phi) (data := data)
  have pulledCoordinate := congrArg Multiplicative.toAdd
    ((rationalFunctionEquiv (Phi := Phi) (data := data) source).apply_symm_apply
      (Multiplicative.ofAdd
        (data.rationalFunctions.pullback (P.base.map arrow)
          (rationalFunctionEquiv (Phi := Phi) (data := data) target alpha).toAdd)))
  change (comparison.map (linearEndomorphismPullback arrow linear alpha).hom).rationalFunction =
      data.rationalFunctions.pullback (comparison.map arrow).base
        (rationalFunctionEquiv (Phi := Phi) (data := data) target alpha).toAdd
    at pulledCoordinate
  apply comparison.map_injective
  rw [comparison.map_comp, comparison.map_comp]
  apply BirationalHom.ext
  · rw [CoAngularPreStepOver.birational_comp_frobeniusDegree,
      CoAngularPreStepOver.birational_comp_frobeniusDegree]
    have pulledLinear := (linearEndomorphismPullback arrow linear alpha).linear
    have arrowLinear := linear
    have alphaLinear := alpha.linear
    change (comparison.map
      (linearEndomorphismPullback arrow linear alpha).hom).frobeniusDegree = 1
      at pulledLinear
    change (comparison.map arrow).frobeniusDegree = 1 at arrowLinear
    change (comparison.map alpha.hom).frobeniusDegree = 1 at alphaLinear
    rw [pulledLinear, arrowLinear, alphaLinear]
  · rw [CoAngularPreStepOver.birational_comp_base,
      CoAngularPreStepOver.birational_comp_base]
    have pulledBase := (linearEndomorphismPullback arrow linear alpha).baseIdentity
    have alphaBase := alpha.baseIdentity
    change (comparison.map
      (linearEndomorphismPullback arrow linear alpha).hom).base = 𝟙 _ at pulledBase
    change (comparison.map alpha.hom).base = 𝟙 _ at alphaBase
    rw [pulledBase, alphaBase]
    simp
  · rw [Iut.SourceModelFrobenioid.birational_comp_rationalFunction,
      Iut.SourceModelFrobenioid.birational_comp_rationalFunction]
    have pulledBase := (linearEndomorphismPullback arrow linear alpha).baseIdentity
    have arrowLinear := linear
    have alphaLinear := alpha.linear
    have alphaCoordinate : (comparison.map alpha.hom).rationalFunction =
        (rationalFunctionEquiv (Phi := Phi) (data := data) target alpha).toAdd := rfl
    change (comparison.map
      (linearEndomorphismPullback arrow linear alpha).hom).base = 𝟙 _ at pulledBase
    change (comparison.map arrow).frobeniusDegree = 1 at arrowLinear
    change (comparison.map alpha.hom).frobeniusDegree = 1 at alphaLinear
    rw [pulledBase, pulledCoordinate, alphaCoordinate, arrowLinear, alphaLinear,
      data.rationalFunctions.pullback_id]
    simp only [AddMonoidHom.id_apply, PNat.val_ofNat, one_nsmul]
    abel

/-- Pullback along an identity arrow is the identity homomorphism. -/
theorem linearEndomorphismPullbackHom_id
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    linearEndomorphismPullbackHom (𝟙 object)
        (P.frobeniusDegree_id object) =
      MonoidHom.id (P.LinearBaseIdentityEndomorphism object) := by
  apply MonoidHom.ext
  intro alpha
  apply (rationalFunctionEquiv (Phi := Phi) (data := data) object).injective
  simp only [linearEndomorphismPullbackHom, MonoidHom.coe_comp,
    Function.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd
      (data.rationalFunctions.pullback (P.base.map (𝟙 object))
        (rationalFunctionEquiv (Phi := Phi) (data := data) object alpha).toAdd) = _
  rw [P.base.map_id, data.rationalFunctions.pullback_id]
  rfl

/-- Rational-function pullback respects composition. -/
theorem linearEndomorphismPullbackHom_comp
    {first middle last :
      ColimitBirationalObject (Phi := Phi) (data := data)}
    (f : first ⟶ middle) (g : middle ⟶ last)
    (fLinear : P.IsLinear f) (gLinear : P.IsLinear g) :
    linearEndomorphismPullbackHom (f ≫ g) (by
        rw [PreFrobenioid.IsLinear, P.frobeniusDegree_comp,
          fLinear, gLinear]
        simp) =
      (linearEndomorphismPullbackHom f fLinear).comp
        (linearEndomorphismPullbackHom g gLinear) := by
  apply MonoidHom.ext
  intro alpha
  apply (rationalFunctionEquiv (Phi := Phi) (data := data) first).injective
  simp only [linearEndomorphismPullbackHom, MonoidHom.coe_comp,
    Function.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd
      (data.rationalFunctions.pullback (P.base.map (f ≫ g))
        (rationalFunctionEquiv (Phi := Phi) (data := data) last alpha).toAdd) =
    Multiplicative.ofAdd
      (data.rationalFunctions.pullback (P.base.map f)
        ((rationalFunctionEquiv (Phi := Phi) (data := data) middle)
          ((rationalFunctionEquiv (Phi := Phi) (data := data) middle).symm
            (Multiplicative.ofAdd
              (data.rationalFunctions.pullback (P.base.map g)
                (rationalFunctionEquiv (Phi := Phi) (data := data)
                  last alpha).toAdd)))).toAdd)
  rw [(rationalFunctionEquiv (Phi := Phi) (data := data) middle).apply_symm_apply]
  rw [P.base.map_comp, data.rationalFunctions.pullback_comp]
  rfl

/-- Proposition 2.2(ii),(iv)'s rational-monoid transport on the actual
Hom-colimit birationalization. -/
def rationalMonoidTransport :
    (preFrobenioid (Phi := Phi) (data := data)).RationalMonoidTransport where
  pullback f := linearEndomorphismPullbackHom f.hom f.linear
  pullback_id X := by
    simpa only [PreFrobenioid.isotropicLinear_id_hom] using
      linearEndomorphismPullbackHom_id (Phi := Phi) (data := data) X.obj
  pullback_comp f g := linearEndomorphismPullbackHom_comp
    f.hom g.hom f.linear g.linear
  hullInclusion object hull :=
    (unitTransport (Phi := Phi) (data := data)
      hull.hom hull.preStep).transport.toMonoidHom
  hullInclusion_injective object hull :=
    (unitTransport (Phi := Phi) (data := data)
      hull.hom hull.preStep).transport.injective

/-- The canonical zero-divisor objects define a linear isotropic section over
the base category. -/
def zeroIsotropicLinearFunctor : D ⥤
    (preFrobenioid (Phi := Phi) (data := data)).IsotropicLinearObject where
  obj base :=
    { obj := zeroObject (Phi := Phi) (data := data) base
      isotropic := isIsotropic _ }
  map {source target} arrow :=
    { hom := (localizationFunctor (Phi := Phi) (data := data)).map
        (Carrier.zeroBaseArrow Phi data arrow)
      linear := by
        change ((comparisonFunctor (Phi := Phi) (data := data)).map
          ((localizationFunctor (Phi := Phi) (data := data)).map
            (Carrier.zeroBaseArrow Phi data arrow))).frobeniusDegree = 1
        rw [comparisonFunctor_map_localizationFunctor]
        rfl }
  map_id object := by
    apply PreFrobenioid.IsotropicLinearHom.ext
    exact (localizationFunctor (Phi := Phi) (data := data)).map_id
      (Carrier.zeroObject Phi data object)
  map_comp first second := by
    apply PreFrobenioid.IsotropicLinearHom.ext
    change (localizationFunctor (Phi := Phi) (data := data)).map
        ((Carrier.zeroBaseFunctor (Phi := Phi) (data := data)).map
          (first ≫ second)) = _
    rw [(Carrier.zeroBaseFunctor (Phi := Phi) (data := data)).map_comp,
      (localizationFunctor (Phi := Phi) (data := data)).map_comp]
    rfl

/-- The full `O^triangle(-)` functor on `D`, before restricting to its units
subfunctor in Proposition 2.2(iii). -/
def rationalMonoidFunctor : Dᵒᵖ ⥤ MonCat.{u} :=
  (zeroIsotropicLinearFunctor (Phi := Phi) (data := data)).op ⋙
    (rationalMonoidTransport (Phi := Phi) (data := data)).functor

/-- The input group-like monoid `B`, regarded as a contravariant functor on
`D` and written multiplicatively. -/
def inputRationalFunctionFunctor : Dᵒᵖ ⥤ MonCat.{u} where
  obj base := MonCat.of (Multiplicative (data.rationalFunctions.obj base.unop))
  map arrow := MonCat.ofHom
    (data.rationalFunctions.pullback arrow.unop).toMultiplicative
  map_id base := by
    apply MonCat.hom_ext
    change (data.rationalFunctions.pullback (𝟙 base.unop)).toMultiplicative = _
    rw [data.rationalFunctions.pullback_id]
    rfl
  map_comp first second := by
    apply MonCat.hom_ext
    change (data.rationalFunctions.pullback (second.unop ≫ first.unop)).toMultiplicative =
      ((data.rationalFunctions.pullback second.unop).toMultiplicative).comp
        (data.rationalFunctions.pullback first.unop).toMultiplicative
    rw [data.rationalFunctions.pullback_comp]
    rfl

/-- The objectwise rational-function equivalence as an isomorphism in
`MonCat`. -/
def rationalFunctionIsoApp (base : Dᵒᵖ) :
    (rationalMonoidFunctor (Phi := Phi) (data := data)).obj base ≅
      (inputRationalFunctionFunctor (data := data)).obj base where
  hom := MonCat.ofHom
    (rationalFunctionEquiv (Phi := Phi) (data := data)
      (zeroObject (Phi := Phi) (data := data) base.unop)).toMonoidHom
  inv := MonCat.ofHom
    (rationalFunctionEquiv (Phi := Phi) (data := data)
      (zeroObject (Phi := Phi) (data := data) base.unop)).symm.toMonoidHom
  hom_inv_id := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro value
    change (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
      (zeroObject (Phi := Phi) (data := data) base.unop) at value
    exact (rationalFunctionEquiv (Phi := Phi) (data := data)
      (zeroObject (Phi := Phi) (data := data) base.unop)).symm_apply_apply value
  inv_hom_id := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro value
    change Multiplicative (data.rationalFunctions.obj base.unop) at value
    exact (rationalFunctionEquiv (Phi := Phi) (data := data)
      (zeroObject (Phi := Phi) (data := data) base.unop)).apply_symm_apply value

/-- Theorem 5.2(ii): the rational-function monoid associated to the actual
Hom-colimit birationalization is naturally isomorphic to `B`. -/
def rationalFunctionNatIso :
    rationalMonoidFunctor (Phi := Phi) (data := data) ≅
      inputRationalFunctionFunctor (data := data) :=
  NatIso.ofComponents
    (rationalFunctionIsoApp (Phi := Phi) (data := data)) (fun {source target} arrow => by
      apply MonCat.hom_ext
      apply MonoidHom.ext
      intro alpha
      change (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
        (zeroObject (Phi := Phi) (data := data) source.unop) at alpha
      let localizedArrow :=
        (localizationFunctor (Phi := Phi) (data := data)).map
          (Carrier.zeroBaseArrow Phi data arrow.unop)
      have baseMap :
          (preFrobenioid (Phi := Phi) (data := data)).base.map localizedArrow =
            arrow.unop := by
        change ((comparisonFunctor (Phi := Phi) (data := data)).map
          localizedArrow).base = arrow.unop
        rw [comparisonFunctor_map_localizationFunctor]
        rfl
      have localizedLinear :
          (preFrobenioid (Phi := Phi) (data := data)).IsLinear localizedArrow := by
        change ((comparisonFunctor (Phi := Phi) (data := data)).map
          localizedArrow).frobeniusDegree = 1
        rw [comparisonFunctor_map_localizationFunctor]
        rfl
      change rationalFunctionEquiv (Phi := Phi) (data := data)
          (zeroObject (Phi := Phi) (data := data) target.unop)
          (linearEndomorphismPullbackHom localizedArrow localizedLinear alpha) =
        Multiplicative.ofAdd
          (data.rationalFunctions.pullback arrow.unop
            (rationalFunctionEquiv (Phi := Phi) (data := data)
              (zeroObject (Phi := Phi) (data := data) source.unop) alpha).toAdd)
      simp only [linearEndomorphismPullbackHom, MonoidHom.coe_comp,
        Function.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [baseMap]
      change (rationalFunctionEquiv (Phi := Phi) (data := data)
          (zeroObject (Phi := Phi) (data := data) target.unop))
          ((rationalFunctionEquiv (Phi := Phi) (data := data)
            (zeroObject (Phi := Phi) (data := data) target.unop)).symm
            (Multiplicative.ofAdd
              (data.rationalFunctions.pullback arrow.unop
                (rationalFunctionEquiv (Phi := Phi) (data := data)
                  (zeroObject (Phi := Phi) (data := data) source.unop) alpha).toAdd))) = _
      rw [(rationalFunctionEquiv (Phi := Phi) (data := data)
        (zeroObject (Phi := Phi) (data := data) target.unop)).apply_symm_apply]
      rfl)

/-- The component of the natural isomorphism commutes with the groupified
divisor map `DivB`, as required by Theorem 5.2(ii). -/
theorem rationalFunctionNatIso_divisor_compatible
    (base : Dᵒᵖ)
    (alpha : (rationalMonoidFunctor (Phi := Phi) (data := data)).obj base) :
    groupifiedDivisorClass (Phi := Phi) (data := data)
        (source := zeroObject (Phi := Phi) (data := data) base.unop)
        (target := zeroObject (Phi := Phi) (data := data) base.unop) alpha.hom =
      data.divisor base.unop
        (((rationalFunctionNatIso (Phi := Phi) (data := data)).hom.app base alpha).toAdd) := by
  change (preFrobenioid (Phi := Phi) (data := data)).LinearBaseIdentityEndomorphism
    (zeroObject (Phi := Phi) (data := data) base.unop) at alpha
  simp only [rationalFunctionNatIso]
  let object := zeroObject (Phi := Phi) (data := data) base.unop
  let value := rationalFunctionEquiv (Phi := Phi) (data := data) object alpha
  have recovered : rationalFunctionEndomorphism
      (Phi := Phi) (data := data) object value = alpha :=
    (rationalFunctionEquiv (Phi := Phi) (data := data) object).symm_apply_apply alpha
  change groupifiedDivisorClass alpha.hom = data.divisor base.unop value.toAdd
  rw [← recovered]
  exact rationalFunctionEndomorphism_groupifiedDivisorClass object value

/-- Every `O^triangle` element determines a literal unit because its
corresponding rational function lies in the group-like monoid `B`. -/
def linearEndomorphismUnit
    (object : ColimitBirationalObject (Phi := Phi) (data := data))
    (alpha : P.LinearBaseIdentityEndomorphism object) :
    Units (P.LinearBaseIdentityEndomorphism object) where
  val := alpha
  inv := (rationalFunctionEquiv (Phi := Phi) (data := data) object).symm
    ((rationalFunctionEquiv (Phi := Phi) (data := data) object alpha)⁻¹)
  val_inv := by
    apply (rationalFunctionEquiv (Phi := Phi) (data := data) object).injective
    rw [map_mul, MulEquiv.apply_symm_apply]
    simp
  inv_val := by
    apply (rationalFunctionEquiv (Phi := Phi) (data := data) object).injective
    rw [map_mul, MulEquiv.apply_symm_apply]
    simp

/-- In the group-like birational target, the literal unit monoid `O^times`
is equivalent to the input rational-function group. -/
def rationalUnitEquiv
    (object : ColimitBirationalObject (Phi := Phi) (data := data)) :
    Units (P.LinearBaseIdentityEndomorphism object) ≃*
      Multiplicative
        (data.rationalFunctions.obj (Object.base object.underlying)) where
  toFun unit := rationalFunctionEquiv (Phi := Phi) (data := data) object unit.1
  invFun value := linearEndomorphismUnit object
    ((rationalFunctionEquiv (Phi := Phi) (data := data) object).symm value)
  left_inv unit := by
    apply Units.ext
    exact (rationalFunctionEquiv (Phi := Phi) (data := data) object).symm_apply_apply
      unit.1
  right_inv value :=
    (rationalFunctionEquiv (Phi := Phi) (data := data) object).apply_symm_apply value
  map_mul' left right :=
    (rationalFunctionEquiv (Phi := Phi) (data := data) object).map_mul left.1 right.1

/-- Proposition 2.2(iii)'s unit subfunctor, i.e. the literal functor
`O^times(-)` on `D` associated to the Hom-colimit birationalization. -/
def rationalUnitFunctor : Dᵒᵖ ⥤ MonCat.{u} where
  obj base := MonCat.of
    (Units ((rationalMonoidFunctor (Phi := Phi) (data := data)).obj base))
  map arrow := MonCat.ofHom
    (Units.map (MonCat.Hom.hom
      ((rationalMonoidFunctor (Phi := Phi) (data := data)).map arrow)))
  map_id base := by
    apply MonCat.hom_ext
    change Units.map (MonCat.Hom.hom
      ((rationalMonoidFunctor (Phi := Phi) (data := data)).map (𝟙 base))) = _
    rw [(rationalMonoidFunctor (Phi := Phi) (data := data)).map_id]
    exact Units.map_id _
  map_comp first second := by
    apply MonCat.hom_ext
    change Units.map (MonCat.Hom.hom
        ((rationalMonoidFunctor (Phi := Phi) (data := data)).map (first ≫ second))) = _
    rw [(rationalMonoidFunctor (Phi := Phi) (data := data)).map_comp]
    exact Units.map_comp _ _

/-- The objectwise `O^times ~= B` equivalence as an isomorphism in
`MonCat`. -/
def rationalUnitIsoApp (base : Dᵒᵖ) :
    (rationalUnitFunctor (Phi := Phi) (data := data)).obj base ≅
      (inputRationalFunctionFunctor (data := data)).obj base where
  hom := MonCat.ofHom
    (rationalUnitEquiv (Phi := Phi) (data := data)
      (zeroObject (Phi := Phi) (data := data) base.unop)).toMonoidHom
  inv := MonCat.ofHom
    (rationalUnitEquiv (Phi := Phi) (data := data)
      (zeroObject (Phi := Phi) (data := data) base.unop)).symm.toMonoidHom
  hom_inv_id := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro value
    exact (rationalUnitEquiv (Phi := Phi) (data := data)
      (zeroObject (Phi := Phi) (data := data) base.unop)).symm_apply_apply value
  inv_hom_id := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro value
    exact (rationalUnitEquiv (Phi := Phi) (data := data)
      (zeroObject (Phi := Phi) (data := data) base.unop)).apply_symm_apply value

/-- Theorem 5.2(ii)'s literal natural isomorphism `O^times(-) ~= B`. -/
def rationalUnitNatIso :
    rationalUnitFunctor (Phi := Phi) (data := data) ≅
      inputRationalFunctionFunctor (data := data) :=
  NatIso.ofComponents
    (rationalUnitIsoApp (Phi := Phi) (data := data)) (fun {source target} arrow => by
      apply MonCat.hom_ext
      apply MonoidHom.ext
      intro alpha
      have naturality := congrArg
        (fun hom => MonCat.Hom.hom hom alpha.1)
        ((rationalFunctionNatIso (Phi := Phi) (data := data)).hom.naturality arrow)
      change MonCat.Hom.hom
          ((rationalFunctionNatIso (Phi := Phi) (data := data)).hom.app target)
          (MonCat.Hom.hom
            ((rationalMonoidFunctor (Phi := Phi) (data := data)).map arrow) alpha.1) =
        MonCat.Hom.hom
          ((inputRationalFunctionFunctor (data := data)).map arrow)
          (MonCat.Hom.hom
            ((rationalFunctionNatIso (Phi := Phi) (data := data)).hom.app source)
            alpha.1)
      exact naturality)

/-- The literal `O^times ~= B` natural isomorphism commutes with `DivB`. -/
theorem rationalUnitNatIso_divisor_compatible
    (base : Dᵒᵖ)
    (alpha : (rationalUnitFunctor (Phi := Phi) (data := data)).obj base) :
    groupifiedDivisorClass (Phi := Phi) (data := data)
        (source := zeroObject (Phi := Phi) (data := data) base.unop)
        (target := zeroObject (Phi := Phi) (data := data) base.unop) alpha.1.hom =
      data.divisor base.unop
        (((rationalUnitNatIso (Phi := Phi) (data := data)).hom.app base alpha).toAdd) := by
  change groupifiedDivisorClass (Phi := Phi) (data := data) alpha.1.hom =
    data.divisor base.unop
      (((rationalFunctionNatIso (Phi := Phi) (data := data)).hom.app base alpha.1).toAdd)
  exact rationalFunctionNatIso_divisor_compatible (Phi := Phi) (data := data)
    base alpha.1

end

end Iut.SourceModelFrobenioid.Carrier.ColimitBirationalObject
