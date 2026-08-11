/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidBasePullbackLift
import Mathlib.Algebra.Category.MonCat.Colimits
import Mathlib.CategoryTheory.Galois.Prorepresentability
import Mathlib.CategoryTheory.Whiskering

/-!
# Evaluation of the Frobenioid rational monoid on a universal pro-object

For a Galois base category with fiber functor, the pointed Galois objects form
the cofiltered presentation of the universal covering pro-object.  This file
evaluates the contravariant functor of Frobenioids I, Proposition 2.2(ii), on
that presentation by taking the corresponding filtered colimit in `MonCat`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Iut.FrobenioidUniversalProEvaluation

universe u

noncomputable section

variable (F : FrobenioidPresentation.{u})

open CategoryTheory.PreGaloisCategory

variable [GaloisCategory (FrobenioidIsotropicBase.DStar F)]
variable (fiber : FrobenioidIsotropicBase.DStar F ⥤ FintypeCat.{u})
variable [FiberFunctor fiber]

/-- The cofiltered system of pointed Galois objects that pro-represents the
chosen fiber functor. -/
abbrev universalCoverIndex := PointedGaloisObject fiber

/-- The underlying projective system of the universal covering pro-object. -/
def universalCoverDiagram :
    universalCoverIndex F fiber ⥤ FrobenioidIsotropicBase.DStar F :=
  PointedGaloisObject.incl fiber

/-- Applying `O^triangle` to the projective system reverses its arrows and
produces the filtered diagram whose colimit is `O^triangle(A)`. -/
def rationalMonoidDiagram :
    (universalCoverIndex F fiber)ᵒᵖ ⥤ MonCat.{u} :=
  (universalCoverDiagram F fiber).op ⋙
    FrobenioidBasePullbackLift.baseRationalMonoidFunctor F

/-- The usual monoid obtained by evaluating `O^triangle` on the universal
covering pro-object. -/
def rationalMonoidAtUniversalCover : MonCat.{u} :=
  colimit (rationalMonoidDiagram F fiber)

/-- The canonical map from a finite pointed Galois level into the evaluated
monoid. -/
def levelMap (level : (universalCoverIndex F fiber)ᵒᵖ) :
    (rationalMonoidDiagram F fiber).obj level ⟶
      rationalMonoidAtUniversalCover F fiber :=
  colimit.ι (rationalMonoidDiagram F fiber) level

omit [FiberFunctor fiber] in
/-- Refining a pointed Galois level does not change the represented element of
the evaluated monoid. -/
theorem levelMap_naturality
    {source target : (universalCoverIndex F fiber)ᵒᵖ}
    (refinement : source ⟶ target) :
    (rationalMonoidDiagram F fiber).map refinement ≫
        levelMap F fiber target =
      levelMap F fiber source := by
  exact colimit.w (rationalMonoidDiagram F fiber) refinement

/-- An element of the inverse limit of the finite Galois automorphism groups
acts levelwise on the universal-cover presentation. -/
def galoisSystemNatIso (g : AutGalois fiber) :
    universalCoverDiagram F fiber ≅ universalCoverDiagram F fiber :=
  NatIso.ofComponents (fun level => g.val level) (by
    intro source target refinement
    change refinement.val ≫ (g.val target).hom =
      (g.val source).hom ≫ refinement.val
    rw [← g.property refinement]
    exact comp_autMap refinement.val (g.val source))

/-- Categorical automorphisms of a monoid are the same group as its bundled
multiplicative automorphisms. -/
private def monCatAutMulEquiv (monoid : MonCat.{u}) :
    Aut monoid ≃* MulAut monoid where
  toFun automorphism := automorphism.monCatIsoToMulEquiv
  invFun automorphism := automorphism.toMonCatIso
  left_inv automorphism := by
    apply Aut.ext
    rfl
  right_inv automorphism := by
    apply MulEquiv.ext
    intro value
    rfl
  map_mul' first second := by
    apply MulEquiv.ext
    intro value
    rfl

/-- The levelwise automorphism induced on the filtered rational-monoid
diagram.  The inverse appears because `O^triangle` is contravariant; this is
the standard conversion from a right pullback operation to a left action. -/
def rationalMonoidDiagramIso (g : AutGalois fiber) :
    rationalMonoidDiagram F fiber ≅ rationalMonoidDiagram F fiber :=
  Functor.isoWhiskerRight (NatIso.op (galoisSystemNatIso F fiber g).symm)
    (FrobenioidBasePullbackLift.baseRationalMonoidFunctor F)

/-- The inverse-limit Galois group acts by automorphisms of the entire
filtered diagram. -/
def rationalMonoidDiagramAction :
    AutGalois fiber →* Aut (rationalMonoidDiagram F fiber) where
  toFun := rationalMonoidDiagramIso F fiber
  map_one' := by
    apply Aut.ext
    apply NatTrans.ext
    funext level
    apply MonCat.hom_ext
    change
      FrobenioidBasePullbackLift.baseArrowPullback F
          level.unop.obj level.unop.obj
            (𝟙 (F.preFrobenioid.base.obj level.unop.obj.object)) =
        MonoidHom.id
          (F.preFrobenioid.LinearBaseIdentityEndomorphism
            level.unop.obj.object)
    exact FrobenioidBasePullbackLift.baseArrowPullback_id F level.unop.obj
  map_mul' first second := by
    apply Aut.ext
    apply NatTrans.ext
    funext level
    apply MonCat.hom_ext
    change
      FrobenioidBasePullbackLift.baseArrowPullback F
          level.unop.obj level.unop.obj
            ((first.val level.unop).inv ≫ (second.val level.unop).inv) =
        (FrobenioidBasePullbackLift.baseArrowPullback F
          level.unop.obj level.unop.obj (first.val level.unop).inv).comp
            (FrobenioidBasePullbackLift.baseArrowPullback F
              level.unop.obj level.unop.obj (second.val level.unop).inv)
    exact FrobenioidBasePullbackLift.baseArrowPullback_comp F
      level.unop.obj level.unop.obj level.unop.obj
        (first.val level.unop).inv (second.val level.unop).inv

/-- IUT II, Definition 4.9(i): the natural action on the monoid obtained by
evaluating `O^triangle` at the universal covering pro-object. -/
def galoisAction :
    AutGalois fiber →* MulAut (rationalMonoidAtUniversalCover F fiber) :=
  (monCatAutMulEquiv (rationalMonoidAtUniversalCover F fiber)).toMonoidHom.comp
    (((colim :
      ((universalCoverIndex F fiber)ᵒᵖ ⥤ MonCat.{u}) ⥤ MonCat.{u}).mapAut
        (rationalMonoidDiagram F fiber)).comp
          (rationalMonoidDiagramAction F fiber))

omit [FiberFunctor fiber] in
/-- At a finite level, the diagram action is the Proposition 2.2(ii)
pullback along the inverse of the corresponding Galois automorphism. -/
theorem rationalMonoidDiagramIso_hom_app
    (g : AutGalois fiber) (level : (universalCoverIndex F fiber)ᵒᵖ) :
    ((rationalMonoidDiagramIso F fiber g).hom.app level).hom =
      FrobenioidBasePullbackLift.baseArrowPullback F
        level.unop.obj level.unop.obj (g.val level.unop).inv :=
  rfl

omit [FiberFunctor fiber] in
/-- The Galois action on the colimit is characterized on every finite-level
representative by rational-monoid pullback along the inverse automorphism. -/
theorem galoisAction_levelMap
    (g : AutGalois fiber) (level : (universalCoverIndex F fiber)ᵒᵖ)
    (value : (rationalMonoidDiagram F fiber).obj level) :
    galoisAction F fiber g (levelMap F fiber level value) =
      levelMap F fiber level
        (FrobenioidBasePullbackLift.baseArrowPullback F
          level.unop.obj level.unop.obj (g.val level.unop).inv value) := by
  change
    ((colim :
      ((universalCoverIndex F fiber)ᵒᵖ ⥤ MonCat.{u}) ⥤ MonCat.{u}).map
        (rationalMonoidDiagramIso F fiber g).hom)
      (levelMap F fiber level value) = _
  have compatibility := colimit.ι_map
    (rationalMonoidDiagramIso F fiber g).hom level
  have compatibilityAt := ConcreteCategory.congr_hom compatibility value
  change
    ((colim :
      ((universalCoverIndex F fiber)ᵒᵖ ⥤ MonCat.{u}) ⥤ MonCat.{u}).map
        (rationalMonoidDiagramIso F fiber g).hom)
          (levelMap F fiber level value) =
      levelMap F fiber level
        (((rationalMonoidDiagramIso F fiber g).hom.app level).hom value)
    at compatibilityAt
  rw [rationalMonoidDiagramIso_hom_app] at compatibilityAt
  exact compatibilityAt

end

end Iut.FrobenioidUniversalProEvaluation
