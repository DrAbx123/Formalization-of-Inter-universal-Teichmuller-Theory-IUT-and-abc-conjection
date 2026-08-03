/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceKernelOrbit
import Iut.Foundations.SourceTemperoid
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Quotients of countable temperoids

For an open continuous surjection `q : Pi → G`, restriction of countable
continuous actions has the kernel-orbit functor as a left adjoint.  The
construction uses the same carrier-level kernel-orbit implementation as finite
covering categories, while preserving countability rather than assuming
finiteness.
-/

namespace Iut

universe u

open CategoryTheory
open scoped SourceCountableTypeCatDiscrete

namespace SourceTemperoidKernelQuotient

variable {Pi G : Type u}
variable [Group Pi] [TopologicalSpace Pi] [IsTopologicalGroup Pi]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (q : Pi →ₜ* G) (surjective : Function.Surjective q)
variable (openMap : IsOpenMap q)

/-- Kernel-orbit carrier of a countable continuous action. -/
abbrev Fiber (X : SourceTemperoidAction Pi) :=
  SourceKernelOrbit.Fiber q X.obj.V.obj

noncomputable instance fiberCountable (X : SourceTemperoidAction Pi) :
    Countable (Fiber q X) :=
  inferInstance

/-- The descended action on kernel orbits. -/
@[reducible]
noncomputable def fiberTargetAction
    (X : SourceTemperoidAction Pi) : MulAction G (Fiber q X) :=
  SourceKernelOrbit.targetAction q surjective X.obj.V.obj

omit [IsTopologicalGroup G] in
@[simp]
theorem smul_mk
    (X : SourceTemperoidAction Pi) (a : Pi) (x : X.obj.V.obj) :
    letI := fiberTargetAction q surjective X
    q a • (Quotient.mk'' x : Fiber q X) = Quotient.mk'' (a • x) :=
  SourceKernelOrbit.smul_mk q surjective X.obj.V.obj a x

/-- The descended action remains continuous. -/
theorem fiberTargetContinuous
    (openMap : IsOpenMap q)
    (X : SourceTemperoidAction Pi) :
    letI := fiberTargetAction q surjective X
    ContinuousSMul G (Fiber q X) := by
  letI : ContinuousSMul Pi X.obj.V.obj := X.property
  exact SourceKernelOrbit.targetContinuous q surjective openMap X.obj.V.obj

/-- The countable continuous `G`-action on kernel-orbit classes. -/
noncomputable def action
    (X : SourceTemperoidAction Pi) : SourceTemperoidAction G := by
  letI := fiberTargetAction q surjective X
  exact
    ⟨SourceCountableTypeCat.ofMulAction G
        (SourceCountableTypeCat.of (Fiber q X)),
      fiberTargetContinuous q surjective openMap X⟩

@[simp]
theorem action_obj_carrier
    (X : SourceTemperoidAction Pi) :
    (action q surjective openMap X).obj.V =
      SourceCountableTypeCat.of (Fiber q X) :=
  rfl

/-- A `Pi`-equivariant map descends to kernel-orbit classes. -/
noncomputable def fiberMap
    {X Y : SourceTemperoidAction Pi} (f : X ⟶ Y) :
    Fiber q X → Fiber q Y :=
  Quotient.map' f.hom.hom (by
    intro x y hxy
    rw [MulAction.orbitRel_apply] at hxy ⊢
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hxy
    refine MulAction.mem_orbit_iff.mpr ⟨k, ?_⟩
    rw [← hk]
    exact (ConcreteCategory.congr_hom (f.hom.comm (k : Pi)) y).symm)

omit [IsTopologicalGroup G] in
@[simp]
theorem fiberMap_mk
    {X Y : SourceTemperoidAction Pi} (f : X ⟶ Y) (x : X.obj.V.obj) :
    fiberMap q f (Quotient.mk'' x) = Quotient.mk'' (f.hom.hom x) :=
  rfl

omit [IsTopologicalGroup G] in
/-- The descended map is equivariant for the target action. -/
theorem fiberMap_smul
    {X Y : SourceTemperoidAction Pi} (f : X ⟶ Y)
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

/-- The morphism on quotient actions induced by an equivariant map. -/
noncomputable def map
    {X Y : SourceTemperoidAction Pi} (f : X ⟶ Y) :
    action q surjective openMap X ⟶ action q surjective openMap Y :=
  ObjectProperty.homMk
    ({ hom := SourceCountableTypeCat.homMk (fiberMap q f)
       comm := fun g => by
         ext z
         exact fiberMap_smul q surjective f g z } :
      (action q surjective openMap X).obj ⟶
        (action q surjective openMap Y).obj)

/-- Kernel orbits as a functor on countable continuous actions. -/
noncomputable def functor :
    SourceTemperoidAction Pi ⥤ SourceTemperoidAction G where
  obj := action q surjective openMap
  map := map q surjective openMap
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

/-- Orbit projection into the restriction of the quotient action. -/
noncomputable def projection
    (X : SourceTemperoidAction Pi) :
    X ⟶ (ContAction.res SourceCountableTypeCat q).obj
      (action q surjective openMap X) :=
  ObjectProperty.homMk
    ({ hom := SourceCountableTypeCat.homMk
          (fun x => (Quotient.mk'' x : Fiber q X))
       comm := fun a => by
         ext x
         exact (smul_mk q surjective X a x).symm } :
      X.obj ⟶
        ((ContAction.res SourceCountableTypeCat q).obj
          (action q surjective openMap X)).obj)

@[simp]
theorem projection_apply
    (X : SourceTemperoidAction Pi) (x : X.obj.V.obj) :
    (projection q surjective openMap X).hom.hom x =
      (Quotient.mk'' x : Fiber q X) :=
  rfl

/-- A map to a restricted `G`-action is constant on kernel orbits. -/
noncomputable def descendFunction
    {X : SourceTemperoidAction Pi}
    {Y : SourceTemperoidAction G}
    (h : X ⟶ (ContAction.res SourceCountableTypeCat q).obj Y) :
    Fiber q X → Y.obj.V.obj :=
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
    rw [qk, map_one]
    rfl)

@[simp]
theorem descendFunction_mk
    {X : SourceTemperoidAction Pi}
    {Y : SourceTemperoidAction G}
    (h : X ⟶ (ContAction.res SourceCountableTypeCat q).obj Y)
    (x : X.obj.V.obj) :
    descendFunction q h (Quotient.mk'' x) = h.hom.hom x :=
  rfl

/-- The descended function is `G`-equivariant. -/
theorem descendFunction_smul
    {X : SourceTemperoidAction Pi}
    {Y : SourceTemperoidAction G}
    (h : X ⟶ (ContAction.res SourceCountableTypeCat q).obj Y)
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

/-- Descend an equivariant map through the orbit quotient. -/
noncomputable def descend
    {X : SourceTemperoidAction Pi}
    {Y : SourceTemperoidAction G}
    (h : X ⟶ (ContAction.res SourceCountableTypeCat q).obj Y) :
    action q surjective openMap X ⟶ Y :=
  ObjectProperty.homMk
    ({ hom := SourceCountableTypeCat.homMk (descendFunction q h)
       comm := fun g => by
         ext z
         exact descendFunction_smul q surjective h g z } :
      (action q surjective openMap X).obj ⟶ Y.obj)

/-- The Hom-set equivalence expressing the orbit/restriction adjunction. -/
noncomputable def homEquiv
    (X : SourceTemperoidAction Pi)
    (Y : SourceTemperoidAction G) :
    (action q surjective openMap X ⟶ Y) ≃
      (X ⟶ (ContAction.res SourceCountableTypeCat q).obj Y) where
  toFun f := projection q surjective openMap X ≫
    (ContAction.res SourceCountableTypeCat q).map f
  invFun := descend q surjective openMap
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

/-- Kernel orbits are left adjoint to restriction on countable temperoids. -/
noncomputable def adjunction :
    functor q surjective openMap ⊣ ContAction.res SourceCountableTypeCat q :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv q surjective openMap
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

/-- Restriction along a surjection is full. -/
noncomputable instance restrictionFull :
    (ContAction.res SourceCountableTypeCat q).Full where
  map_surjective {X Y} f := by
    refine ⟨ObjectProperty.homMk
      ({ hom := f.hom.hom
         comm := fun g => by
           obtain ⟨a, rfl⟩ := surjective g
           exact f.hom.comm a } : X.obj ⟶ Y.obj), ?_⟩
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    rfl

/-- Restriction is faithful. -/
instance restrictionFaithful :
    (ContAction.res SourceCountableTypeCat q).Faithful where
  map_injective {X Y} {f g} equality := by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    exact congrArg (fun h => h.hom.hom) equality

/-- Connectedness is preserved by restriction along a surjection. -/
theorem restriction_connected
    (surjective : Function.Surjective q)
    (X : SourceTemperoidAction G)
    (connected : sourceConnectedTemperoidAction G X) :
    sourceConnectedTemperoidAction Pi
      ((ContAction.res SourceCountableTypeCat q).obj X) := by
  constructor
  · exact connected.1
  · constructor
    intro first second
    obtain ⟨g, hg⟩ := connected.2.exists_smul_eq first second
    obtain ⟨a, rfl⟩ := surjective g
    exact ⟨a, hg⟩

/-- Kernel orbits preserve connectedness. -/
theorem action_connected
    (X : SourceTemperoidAction Pi)
    (connected : sourceConnectedTemperoidAction Pi X) :
    sourceConnectedTemperoidAction G (action q surjective openMap X) := by
  letI := fiberTargetAction q surjective X
  constructor
  · exact Nonempty.map (fun x => (Quotient.mk'' x : Fiber q X)) connected.1
  · constructor
    intro first second
    induction first using Quotient.inductionOn' with
    | _ first =>
        induction second using Quotient.inductionOn' with
        | _ second =>
            obtain ⟨a, ha⟩ := connected.2.exists_smul_eq first second
            refine ⟨q a, ?_⟩
            change q a • (Quotient.mk'' first : Fiber q X) =
              Quotient.mk'' second
            rw [smul_mk q surjective X]
            exact congrArg Quotient.mk'' ha

/-- Restriction on connected temperoids. -/
noncomputable def connectedRestriction :
    SourceConnectedTemperoid G ⥤ SourceConnectedTemperoid Pi where
  obj X := ⟨(ContAction.res SourceCountableTypeCat q).obj X.obj,
    restriction_connected q surjective X.obj X.property⟩
  map f := ObjectProperty.homMk
    ((ContAction.res SourceCountableTypeCat q).map f.hom)
  map_id X := by apply ObjectProperty.hom_ext; rfl
  map_comp f g := by apply ObjectProperty.hom_ext; rfl

/-- Kernel orbits on connected temperoids. -/
noncomputable def connectedFunctor :
    SourceConnectedTemperoid Pi ⥤ SourceConnectedTemperoid G where
  obj X := ⟨action q surjective openMap X.obj,
    action_connected q surjective openMap X.obj X.property⟩
  map f := ObjectProperty.homMk (map q surjective openMap f.hom)
  map_id X := by
    apply ObjectProperty.hom_ext
    exact (functor q surjective openMap).map_id X.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (functor q surjective openMap).map_comp f.hom g.hom

instance connectedRestrictionFaithful :
    (connectedRestriction q surjective).Faithful where
  map_injective {X Y} {f g} equality := by
    apply ObjectProperty.hom_ext
    apply (ContAction.res SourceCountableTypeCat q).map_injective
    exact congrArg (fun h => h.hom) equality

noncomputable instance connectedRestrictionFull :
    (connectedRestriction q surjective).Full where
  map_surjective {X Y} f := by
    letI := restrictionFull q surjective
    let lifted : X.obj ⟶ Y.obj :=
      (ContAction.res SourceCountableTypeCat q).preimage f.hom
    refine ⟨ObjectProperty.homMk lifted, ?_⟩
    apply ObjectProperty.hom_ext
    exact (ContAction.res SourceCountableTypeCat q).map_preimage f.hom

/-- Restriction on connected temperoids is fully faithful. -/
noncomputable def connectedRestrictionFullyFaithful :
    (connectedRestriction q surjective).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful (connectedRestriction q surjective)

noncomputable def connectedFunctorCompInclusionIso :
    (sourceConnectedTemperoidAction Pi).ι ⋙ functor q surjective openMap ≅
      connectedFunctor q surjective openMap ⋙
        (sourceConnectedTemperoidAction G).ι :=
  Iso.refl _

noncomputable def connectedRestrictionCompInclusionIso :
    (sourceConnectedTemperoidAction G).ι ⋙
        ContAction.res SourceCountableTypeCat q ≅
      connectedRestriction q surjective ⋙
        (sourceConnectedTemperoidAction Pi).ι :=
  Iso.refl _

/-- The orbit/restriction adjunction restricts to connected temperoids. -/
noncomputable def connectedAdjunction :
    connectedFunctor q surjective openMap ⊣ connectedRestriction q surjective :=
  (adjunction q surjective openMap).restrictFullyFaithful
    (sourceConnectedTemperoidAction Pi).fullyFaithfulι
    (sourceConnectedTemperoidAction G).fullyFaithfulι
    (connectedFunctorCompInclusionIso q surjective openMap)
    (connectedRestrictionCompInclusionIso q surjective)

end SourceTemperoidKernelQuotient

end Iut
