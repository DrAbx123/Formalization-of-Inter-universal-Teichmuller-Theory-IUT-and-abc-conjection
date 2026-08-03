/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceConnectedCoveringCategory
import Iut.Foundations.SourceKernelOrbit
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Quotients of connected covering categories

For a surjection `q : Π → G` of profinite groups, pullback of finite covers is
restriction of actions `B(G) → B(Π)`.  Its left adjoint sends a finite
continuous `Π`-set to its orbits under `ker(q)`.  This file constructs that
orbit action and the resulting adjunction.  The connected restriction gives
the source inclusion `B(G)⁰ ⊆ B(Π)⁰` used for the base-field boundary of
the IUT local covering categories.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits
open scoped FintypeCatDiscrete

namespace SourceActionKernelQuotient

variable {Pi G : ProfiniteGrp.{u}}
variable (q : Pi ⟶ G) (surjective : Function.Surjective q)

/-- The fiber set after dividing a finite `Π`-action by the action of
`ker(q)`. -/
abbrev Fiber (X : ContAction FintypeCat.{u} Pi) :=
  SourceKernelOrbit.Fiber q.hom X.obj.V

noncomputable instance fiberFintype (X : ContAction FintypeCat.{u} Pi) :
    Fintype (Fiber q X) :=
  Fintype.ofFinite _

/-- Transport the quotient action across the first-isomorphism equivalence
`Π/ker(q) ≃ G`. -/
@[reducible]
noncomputable def fiberTargetAction
    (X : ContAction FintypeCat.{u} Pi) : MulAction G (Fiber q X) :=
  SourceKernelOrbit.targetAction q.hom surjective X.obj.V

/-- The transported `G`-action restricts along `q` to the original action on
kernel-orbit classes. -/
@[simp]
theorem smul_mk
    (X : ContAction FintypeCat.{u} Pi) (a : Pi) (x : X.obj.V) :
    letI := fiberTargetAction q surjective X
    q a • (Quotient.mk'' x : Fiber q X) = Quotient.mk'' (a • x) :=
  SourceKernelOrbit.smul_mk q.hom surjective X.obj.V a x

/-- The transported finite `G`-action is continuous. -/
theorem fiberTargetContinuous
    (X : ContAction FintypeCat.{u} Pi) :
    letI := fiberTargetAction q surjective X
    ContinuousSMul G (Fiber q X) := by
  letI : ContinuousSMul Pi X.obj.V := X.property
  have quotientMap : Topology.IsQuotientMap q :=
    IsQuotientMap.of_surjective_continuous surjective q.hom.continuous
  have openMap : IsOpenMap q :=
    (MonoidHom.isOpenQuotientMap_of_isQuotientMap
      (φ := q.hom.toMonoidHom) quotientMap).isOpenMap
  exact SourceKernelOrbit.targetContinuous q.hom surjective openMap X.obj.V

/-- The continuous `G`-action of kernel-orbit classes. -/
noncomputable def action
    (X : ContAction FintypeCat.{u} Pi) :
    ContAction FintypeCat.{u} G := by
  letI := fiberTargetAction q surjective X
  exact
    ⟨Action.FintypeCat.ofMulAction G (FintypeCat.of (Fiber q X)),
      fiberTargetContinuous q surjective X⟩

@[simp]
theorem action_obj_carrier
    (X : ContAction FintypeCat.{u} Pi) :
    (action q surjective X).obj.V = FintypeCat.of (Fiber q X) :=
  rfl

/-- A `Π`-equivariant map descends to a map on kernel-orbit fibers. -/
noncomputable def fiberMap
    {X Y : ContAction FintypeCat.{u} Pi} (f : X ⟶ Y) :
    Fiber q X → Fiber q Y :=
  Quotient.map' f.hom.hom (by
    intro x y hxy
    rw [MulAction.orbitRel_apply] at hxy ⊢
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hxy
    refine MulAction.mem_orbit_iff.mpr ⟨k, ?_⟩
    rw [← hk]
    exact (ConcreteCategory.congr_hom (f.hom.comm (k : Pi)) y).symm)

@[simp]
theorem fiberMap_mk
    {X Y : ContAction FintypeCat.{u} Pi} (f : X ⟶ Y) (x : X.obj.V) :
    fiberMap q f (Quotient.mk'' x) = Quotient.mk'' (f.hom.hom x) :=
  rfl

/-- The descended map is equivariant for the transported target actions. -/
theorem fiberMap_smul
    {X Y : ContAction FintypeCat.{u} Pi} (f : X ⟶ Y)
    (g : G) (z : Fiber q X) :
    letI := fiberTargetAction q surjective X
    letI := fiberTargetAction q surjective Y
    fiberMap q f (g • z) = g • fiberMap q f z := by
  letI := fiberTargetAction q surjective X
  letI := fiberTargetAction q surjective Y
  obtain ⟨a, rfl⟩ := surjective g
  induction z using Quotient.inductionOn' with
  | _ x =>
      rw [smul_mk q surjective X, fiberMap_mk,
        fiberMap_mk, smul_mk q surjective Y]
      apply congrArg Quotient.mk''
      exact ConcreteCategory.congr_hom (f.hom.comm a) x

/-- The morphism on continuous quotient actions induced by an equivariant map. -/
noncomputable def map
    {X Y : ContAction FintypeCat.{u} Pi} (f : X ⟶ Y) :
    action q surjective X ⟶ action q surjective Y :=
  ObjectProperty.homMk
    ({ hom := FintypeCat.homMk (fiberMap q f)
       comm := fun g => by
         ext z
         exact fiberMap_smul q surjective f g z } :
      (action q surjective X).obj ⟶ (action q surjective Y).obj)

/-- Kernel orbits define the left-adjoint functor on finite continuous
actions. -/
noncomputable def functor :
    ContAction FintypeCat.{u} Pi ⥤ ContAction FintypeCat.{u} G where
  obj := action q surjective
  map := map q surjective
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext z
    induction z using Quotient.inductionOn' with
    | _ x => rfl
  map_comp {X Y Z} f g := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext z
    induction z using Quotient.inductionOn' with
    | _ x => rfl

/-- The orbit projection, as a morphism from a `Π`-action to the
restriction of its quotient `G`-action. -/
noncomputable def projection
    (X : ContAction FintypeCat.{u} Pi) :
    X ⟶ (ContAction.res FintypeCat q.hom).obj (action q surjective X) :=
  ObjectProperty.homMk
    ({ hom := FintypeCat.homMk (fun x =>
          (Quotient.mk'' x : Fiber q X))
       comm := fun a => by
         ext x
         exact (smul_mk q surjective X a x).symm } :
      X.obj ⟶
        ((ContAction.res FintypeCat q.hom).obj
          (action q surjective X)).obj)

@[simp]
theorem projection_apply
    (X : ContAction FintypeCat.{u} Pi) (x : X.obj.V) :
    (projection q surjective X).hom.hom x =
      (Quotient.mk'' x : Fiber q X) :=
  rfl

/-- A map from a `Π`-action to a restricted `G`-action is constant on
`ker(q)`-orbits. -/
noncomputable def descendFunction
    {X : ContAction FintypeCat.{u} Pi}
    {Y : ContAction FintypeCat.{u} G}
    (h : X ⟶ (ContAction.res FintypeCat q.hom).obj Y) :
    Fiber q X → Y.obj.V :=
  fun z => Quotient.liftOn' z h.hom.hom (by
    intro x y hxy
    rw [MulAction.orbitRel_apply] at hxy
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hxy
    rw [← hk]
    have equivariance :
        h.hom.hom ((k : Pi) • y) =
          (Y.obj.ρ (q k)).hom (h.hom.hom y) :=
      ConcreteCategory.congr_hom (h.hom.comm (k : Pi)) y
    change h.hom.hom ((k : Pi) • y) = h.hom.hom y
    rw [equivariance]
    have qk : q (k : Pi) = 1 := MonoidHom.mem_ker.mp k.property
    rw [qk]
    rw [map_one]
    rfl)

@[simp]
theorem descendFunction_mk
    {X : ContAction FintypeCat.{u} Pi}
    {Y : ContAction FintypeCat.{u} G}
    (h : X ⟶ (ContAction.res FintypeCat q.hom).obj Y)
    (x : X.obj.V) :
    descendFunction q h (Quotient.mk'' x) = h.hom.hom x :=
  rfl

/-- The descended function is `G`-equivariant. -/
theorem descendFunction_smul
    {X : ContAction FintypeCat.{u} Pi}
    {Y : ContAction FintypeCat.{u} G}
    (h : X ⟶ (ContAction.res FintypeCat q.hom).obj Y)
    (g : G) (z : Fiber q X) :
    letI := fiberTargetAction q surjective X
    descendFunction q h (g • z) = g • descendFunction q h z := by
  letI := fiberTargetAction q surjective X
  obtain ⟨a, rfl⟩ := surjective g
  induction z using Quotient.inductionOn' with
  | _ x =>
      rw [smul_mk q surjective X, descendFunction_mk,
        descendFunction_mk]
      exact ConcreteCategory.congr_hom (h.hom.comm a) x

/-- Descend an equivariant map through the kernel-orbit quotient. -/
noncomputable def descend
    {X : ContAction FintypeCat.{u} Pi}
    {Y : ContAction FintypeCat.{u} G}
    (h : X ⟶ (ContAction.res FintypeCat q.hom).obj Y) :
    action q surjective X ⟶ Y :=
  ObjectProperty.homMk
    ({ hom := FintypeCat.homMk (descendFunction q h)
       comm := fun g => by
         ext z
         exact descendFunction_smul q surjective h g z } :
      (action q surjective X).obj ⟶ Y.obj)

/-- The explicit Hom-set equivalence between kernel orbits and restriction. -/
noncomputable def homEquiv
    (X : ContAction FintypeCat.{u} Pi)
    (Y : ContAction FintypeCat.{u} G) :
    (action q surjective X ⟶ Y) ≃
      (X ⟶ (ContAction.res FintypeCat q.hom).obj Y) where
  toFun f :=
    projection q surjective X ≫
      (ContAction.res FintypeCat q.hom).map f
  invFun := descend q surjective
  left_inv f := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext z
    induction z using Quotient.inductionOn' with
    | _ x => rfl
  right_inv h := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext x
    rfl

/-- Kernel orbits are left adjoint to restriction along a surjection of
profinite groups. -/
noncomputable def adjunction :
    functor q surjective ⊣ ContAction.res FintypeCat q.hom :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv q surjective
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        ext z
        induction z using Quotient.inductionOn' with
        | _ x => rfl
      homEquiv_naturality_right := by
        intro X Y Y' f g
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        ext x
        rfl }

/-- Restriction along a surjection is full on finite continuous actions. -/
noncomputable instance restrictionFull :
    (ContAction.res FintypeCat q.hom).Full where
  map_surjective {X Y} f := by
    refine ⟨ObjectProperty.homMk
      ({ hom := f.hom.hom
         comm := fun g => by
           obtain ⟨a, rfl⟩ := surjective g
           exact f.hom.comm a } : X.obj ⟶ Y.obj), ?_⟩
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    rfl

/-- Restriction along any continuous homomorphism is faithful. -/
instance restrictionFaithful :
    (ContAction.res FintypeCat q.hom).Faithful where
  map_injective {X Y} {f g} equality := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    exact congrArg (fun h => h.hom.hom) equality

/-- A connected `G`-action remains connected after restriction along the
surjection `q`. -/
theorem restriction_isConnected
    (surjective : Function.Surjective q)
    (X : ContAction FintypeCat.{u} G)
    (connected : PreGaloisCategory.IsConnected X) :
    PreGaloisCategory.IsConnected
      ((ContAction.res FintypeCat q.hom).obj X) := by
  letI : PreGaloisCategory.IsConnected X := connected
  haveI : Nonempty X.obj.V := by
    change Nonempty ((continuousActionFiber G).obj X)
    infer_instance
  have sourceNonempty :
      Nonempty (((ContAction.res FintypeCat q.hom).obj X).obj.V) :=
    inferInstanceAs (Nonempty X.obj.V)
  letI : Nonempty (((ContAction.res FintypeCat q.hom).obj X).obj.V) :=
    sourceNonempty
  apply (SourceConnectedCoveringCategory.connected_iff_pretransitive Pi _).mpr
  have targetTransitive := continuousAction_pretransitive_of_isConnected G X
  constructor
  intro first second
  obtain ⟨g, hg⟩ := targetTransitive.exists_smul_eq first second
  obtain ⟨a, rfl⟩ := surjective g
  exact ⟨a, hg⟩

/-- Kernel orbits of a connected `Π`-action form a connected `G`-action. -/
theorem action_isConnected
    (X : ContAction FintypeCat.{u} Pi)
    (connected : PreGaloisCategory.IsConnected X) :
    PreGaloisCategory.IsConnected (action q surjective X) := by
  letI := fiberTargetAction q surjective X
  letI : PreGaloisCategory.IsConnected X := connected
  haveI : Nonempty X.obj.V := by
    change Nonempty ((continuousActionFiber Pi).obj X)
    infer_instance
  have quotientNonempty : Nonempty (Fiber q X) :=
    Nonempty.map (fun x => (Quotient.mk'' x : Fiber q X)) inferInstance
  letI : Nonempty (action q surjective X).obj.V := quotientNonempty
  apply (SourceConnectedCoveringCategory.connected_iff_pretransitive G _).mpr
  have sourceTransitive := continuousAction_pretransitive_of_isConnected Pi X
  constructor
  intro first second
  induction first using Quotient.inductionOn' with
  | _ first =>
      induction second using Quotient.inductionOn' with
      | _ second =>
          obtain ⟨a, ha⟩ := sourceTransitive.exists_smul_eq first second
          refine ⟨q a, ?_⟩
          change q a • (Quotient.mk'' first : Fiber q X) =
            Quotient.mk'' second
          rw [smul_mk q surjective X]
          exact congrArg Quotient.mk'' ha

/-- Restriction on the connected covering subcategories. -/
noncomputable def connectedRestriction :
    SourceConnectedCoveringCategory G ⥤
      SourceConnectedCoveringCategory Pi where
  obj X :=
    ⟨(ContAction.res FintypeCat q.hom).obj X.obj,
      restriction_isConnected q surjective X.obj X.property⟩
  map f := ObjectProperty.homMk
    ((ContAction.res FintypeCat q.hom).map f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    rfl

/-- Kernel orbits on the connected covering subcategories. -/
noncomputable def connectedFunctor :
    SourceConnectedCoveringCategory Pi ⥤
      SourceConnectedCoveringCategory G where
  obj X := ⟨action q surjective X.obj,
    action_isConnected q surjective X.obj X.property⟩
  map f := ObjectProperty.homMk (map q surjective f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact (functor q surjective).map_id X.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (functor q surjective).map_comp f.hom g.hom

/-- The connected restriction is faithful. -/
instance connectedRestrictionFaithful :
    (connectedRestriction q surjective).Faithful where
  map_injective {X Y} {f g} equality := by
    apply ObjectProperty.hom_ext
    apply (ContAction.res FintypeCat q.hom).map_injective
    exact congrArg (fun h => h.hom) equality

/-- The connected restriction is full. -/
noncomputable instance connectedRestrictionFull :
    (connectedRestriction q surjective).Full where
  map_surjective {X Y} f := by
    letI := restrictionFull q surjective
    let lifted : X.obj ⟶ Y.obj :=
      (ContAction.res FintypeCat q.hom).preimage f.hom
    refine ⟨ObjectProperty.homMk lifted, ?_⟩
    apply ObjectProperty.hom_ext
    exact (ContAction.res FintypeCat q.hom).map_preimage f.hom

/-- The connected quotient functor commutes with the full-subcategory
inclusions. -/
noncomputable def connectedFunctorCompInclusionIso :
    (sourceConnectedContinuousAction Pi).ι ⋙ functor q surjective ≅
      connectedFunctor q surjective ⋙
        (sourceConnectedContinuousAction G).ι :=
  Iso.refl _

/-- Connected restriction commutes with the full-subcategory inclusions. -/
noncomputable def connectedRestrictionCompInclusionIso :
    (sourceConnectedContinuousAction G).ι ⋙
        ContAction.res FintypeCat q.hom ≅
      connectedRestriction q surjective ⋙
        (sourceConnectedContinuousAction Pi).ι :=
  Iso.refl _

/-- The kernel-orbit/restriction adjunction restricts to connected covering
categories. -/
noncomputable def connectedAdjunction :
    connectedFunctor q surjective ⊣ connectedRestriction q surjective :=
  (adjunction q surjective).restrictFullyFaithful
    (sourceConnectedContinuousAction Pi).fullyFaithfulι
    (sourceConnectedContinuousAction G).fullyFaithfulι
    (connectedFunctorCompInclusionIso q surjective)
    (connectedRestrictionCompInclusionIso q surjective)

end SourceActionKernelQuotient

end Iut
