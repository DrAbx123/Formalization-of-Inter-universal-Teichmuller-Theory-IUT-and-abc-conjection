/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceAnabelioidSlice
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Components of slices of continuous-action anabelioids

Proposition 1.2.1(i) of Mochizuki's *The Geometry of Anabelioids* states
that the slice `X_S` is an anabelioid whose connected components are naturally
indexed by the connected components of `S`.

For `X = B(G)`, the components of `S` are its `G`-orbits.  This file constructs
the orbit actions, restricts every object over `S` to each orbit, and proves
that the resulting functor from `B(G)_S` to the product of the orbit slices is
an equivalence.  It then identifies every factor with the connected
anabelioid of the open stabilizer of a representative.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits
open scoped FintypeCatDiscrete

/-! ## The orbit index and its transitive component actions -/

/-- The finite set of connected components of a finite continuous `G`-set. -/
abbrev SourceActionComponent
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :=
  MulAction.orbitRel.Quotient G S.obj.V

noncomputable instance sourceActionComponent_fintype
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :
    Fintype (SourceActionComponent G S) :=
  Fintype.ofFinite _

/-- The fiber of the orbit quotient over a component. -/
abbrev SourceActionComponentFiber
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :=
  { s : S.obj.V // Quotient.mk'' s = component }

namespace SourceActionComponentFiber

variable
    (G : ProfiniteGrp.{u})
    (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S)

noncomputable instance : Fintype (SourceActionComponentFiber G S component) :=
  Fintype.ofFinite _

instance : SMul G (SourceActionComponentFiber G S component) where
  smul g s :=
    ⟨g • s.1, by
      have horbit :
          (Quotient.mk'' (g • s.1) : SourceActionComponent G S) =
            (Quotient.mk'' s.1 : SourceActionComponent G S) := by
        exact Quotient.sound
          (s := MulAction.orbitRel G S.obj.V)
          ((MulAction.orbitRel_apply).2
            (MulAction.mem_orbit s.1 g))
      exact horbit.trans s.2⟩

instance : MulAction G (SourceActionComponentFiber G S component) where
  one_smul s := by
    apply Subtype.ext
    exact one_smul G s.1
  mul_smul first second s := by
    apply Subtype.ext
    exact mul_smul first second s.1

@[simp]
theorem smul_val
    (g : G) (s : SourceActionComponentFiber G S component) :
    (g • s).1 = g • s.1 :=
  rfl

noncomputable instance : TopologicalSpace
    (SourceActionComponentFiber G S component) := ⊥

instance : DiscreteTopology (SourceActionComponentFiber G S component) :=
  ⟨rfl⟩

end SourceActionComponentFiber

/-- The transitive continuous action carried by one orbit of `S`. -/
noncomputable def sourceActionComponentAction
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    ContAction FintypeCat.{u} G := by
  refine
    ⟨Action.FintypeCat.ofMulAction G
      (FintypeCat.of (SourceActionComponentFiber G S component)), ?_⟩
  change ContinuousSMul G (SourceActionComponentFiber G S component)
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro s
  haveI : ContinuousSMul G S.obj.V := S.property
  have hopen :
      IsOpen (MulAction.stabilizer G s.1 : Set G) :=
    stabilizer_isOpen G s.1
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer G s.1)
    (H₂ := MulAction.stabilizer G s) _ hopen
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  apply Subtype.ext
  exact hg

/-- Inclusion of one orbit action into `S`. -/
noncomputable def sourceActionComponentInclusion
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    sourceActionComponentAction G S component ⟶ S :=
  ObjectProperty.homMk
    ({ hom := FintypeCat.homMk Subtype.val
       comm := fun _ => rfl } :
      (sourceActionComponentAction G S component).obj ⟶ S.obj)

/-- The orbit actions reconstruct the underlying finite set of `S`. -/
noncomputable def sourceActionComponentSigmaEquiv
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :
    (Σ component : SourceActionComponent G S,
      SourceActionComponentFiber G S component) ≃ S.obj.V :=
  Equiv.sigmaFiberEquiv
    (fun s : S.obj.V => (Quotient.mk'' s : SourceActionComponent G S))

@[simp]
theorem sourceActionComponentSigmaEquiv_apply
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (point : Σ component : SourceActionComponent G S,
      SourceActionComponentFiber G S component) :
    sourceActionComponentSigmaEquiv G S point = point.2.1 :=
  rfl

/-- Every orbit action is transitive. -/
theorem sourceActionComponentAction_pretransitive
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    MulAction.IsPretransitive G
      (sourceActionComponentAction G S component).obj.V := by
  constructor
  intro first second
  have horbit :
      second.1 ∈ MulAction.orbit G first.1 := by
    rw [← MulAction.orbitRel_apply, ← Quotient.eq'']
    exact second.2.trans first.2.symm
  rcases MulAction.mem_orbit_iff.mp horbit with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact hg

/-! ## Identification of an orbit with an open-stabilizer coset action -/

/-- The stabilizer of the canonical representative of an orbit component,
bundled as an open subgroup. -/
noncomputable def sourceActionComponentOpenStabilizer
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    OpenSubgroup G where
  toSubgroup :=
    MulAction.stabilizer G component.out
  isOpen' := by
    haveI : ContinuousSMul G S.obj.V := S.property
    exact stabilizer_isOpen G component.out

/-- The open stabilizer, also bundled as a closed subgroup so that its
inherited profinite structure is available to the Galois-category package. -/
noncomputable def sourceActionComponentClosedStabilizer
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    ClosedSubgroup G where
  toSubgroup :=
    (sourceActionComponentOpenStabilizer
      G S component).toSubgroup
  isClosed' :=
    Subgroup.isClosed_of_isOpen
      (sourceActionComponentOpenStabilizer
        G S component).toSubgroup
      (sourceActionComponentOpenStabilizer
        G S component).isOpen

/-- The profinite group carried by the open stabilizer. -/
noncomputable def sourceActionComponentStabilizerProfiniteGroup
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    ProfiniteGrp.{u} := by
  let H := sourceActionComponentOpenStabilizer G S component
  letI : IsTopologicalGroup H :=
    inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  letI : CompactSpace H :=
    isCompact_iff_compactSpace.mp
      (IsClosed.isCompact
        (Subgroup.isClosed_of_isOpen H.toSubgroup H.isOpen))
  exact ProfiniteGrp.of H

/-- The quotient fiber representing one component is the usual orbit of its
canonical representative. -/
noncomputable def sourceActionComponentFiberOrbitEquiv
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    SourceActionComponentFiber G S component ≃
      MulAction.orbit G component.out where
  toFun point :=
    ⟨point.1, by
      rw [← MulAction.orbitRel_apply, ← Quotient.eq'']
      exact point.2.trans (Quotient.out_eq' component).symm⟩
  invFun point :=
    ⟨point.1, by
      have horbit :
          (Quotient.mk'' point.1 : SourceActionComponent G S) =
            (Quotient.mk'' component.out :
              SourceActionComponent G S) := by
        rw [Quotient.eq'', MulAction.orbitRel_apply]
        exact point.2
      exact horbit.trans (Quotient.out_eq' component)⟩
  left_inv point := by
    apply Subtype.ext
    rfl
  right_inv point := by
    apply Subtype.ext
    rfl

/-- Orbit-stabilizer identifies a component fiber with the cosets of the open
stabilizer of its canonical representative. -/
noncomputable def sourceActionComponentCosetEquiv
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    SourceActionComponentFiber G S component ≃
      G ⧸ (sourceActionComponentOpenStabilizer
        G S component).toSubgroup :=
  (sourceActionComponentFiberOrbitEquiv G S component).trans
    (MulAction.orbitEquivQuotientStabilizer
      G component.out)

/-- The inverse orbit-stabilizer map sends a coset to its translate of the
canonical representative. -/
@[simp]
theorem sourceActionComponentCosetEquiv_symm_apply_val
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S)
    (coset :
      G ⧸ (sourceActionComponentOpenStabilizer
        G S component).toSubgroup) :
    ((sourceActionComponentCosetEquiv G S component).symm coset).1 =
      MulAction.ofQuotientStabilizer G component.out coset :=
  rfl

/-- The inverse orbit-stabilizer map is `G`-equivariant. -/
theorem sourceActionComponentCosetEquiv_symm_smul
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S)
    (g : G)
    (coset :
      G ⧸ (sourceActionComponentOpenStabilizer
        G S component).toSubgroup) :
    (sourceActionComponentCosetEquiv G S component).symm
        (g • coset) =
      g • (sourceActionComponentCosetEquiv G S component).symm
        coset := by
  apply Subtype.ext
  exact
    MulAction.ofQuotientStabilizer_smul
      G component.out g coset

/-- The orbit-stabilizer map is `G`-equivariant. -/
theorem sourceActionComponentCosetEquiv_smul
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S)
    (g : G) (point : SourceActionComponentFiber G S component) :
    sourceActionComponentCosetEquiv G S component (g • point) =
      g • sourceActionComponentCosetEquiv G S component point := by
  apply
    (sourceActionComponentCosetEquiv G S component).symm.injective
  rw [Equiv.symm_apply_apply]
  rw [sourceActionComponentCosetEquiv_symm_smul]
  rw [Equiv.symm_apply_apply]

/-- The component action is isomorphic to the transitive coset action of its
open stabilizer. -/
noncomputable def sourceActionComponentCosetActionIso
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    sourceActionComponentAction G S component ≅
      sourceOpenCosetAction G
        (sourceActionComponentOpenStabilizer G S component) := by
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ ?_
  · change
      FintypeCat.of
          (SourceActionComponentFiber G S component) ≅
        FintypeCat.of
          (G ⧸ (sourceActionComponentOpenStabilizer
            G S component).toSubgroup)
    exact FintypeCat.equivEquivIso
      (sourceActionComponentCosetEquiv G S component)
  · intro g
    ext point
    exact
      sourceActionComponentCosetEquiv_smul
        G S component g point

/-! ## Restriction of a slice object to an orbit -/

/-- The points of `T -> S` lying over one orbit of `S`. -/
abbrev SourceSliceComponentCarrier
    {G : ProfiniteGrp.{u}} {S : ContAction FintypeCat.{u} G}
    (T : Over S) (component : SourceActionComponent G S) :=
  { t : T.left.obj.V //
    Quotient.mk'' (T.hom.hom.hom t) = component }

namespace SourceSliceComponentCarrier

variable
    {G : ProfiniteGrp.{u}}
    {S : ContAction FintypeCat.{u} G}
    (T : Over S)
    (component : SourceActionComponent G S)

noncomputable instance : Fintype (SourceSliceComponentCarrier T component) :=
  Fintype.ofFinite _

instance : SMul G (SourceSliceComponentCarrier T component) where
  smul g t :=
    ⟨g • t.1, by
      have hequivariant :=
        ConcreteCategory.congr_hom (T.hom.hom.comm g) t.1
      have hequivariant' :
          T.hom.hom.hom (g • t.1) =
            g • T.hom.hom.hom t.1 := by
        simpa only [FintypeCat.comp_apply] using hequivariant
      have horbit :
          (Quotient.mk''
              (T.hom.hom.hom (g • t.1)) :
                SourceActionComponent G S) =
            (Quotient.mk'' (T.hom.hom.hom t.1) :
              SourceActionComponent G S) := by
        rw [hequivariant']
        exact Quotient.sound
          (s := MulAction.orbitRel G S.obj.V)
          ((MulAction.orbitRel_apply).2
            (MulAction.mem_orbit (T.hom.hom.hom t.1) g))
      exact horbit.trans t.2⟩

instance : MulAction G (SourceSliceComponentCarrier T component) where
  one_smul t := by
    apply Subtype.ext
    exact one_smul G t.1
  mul_smul first second t := by
    apply Subtype.ext
    exact mul_smul first second t.1

@[simp]
theorem smul_val
    (g : G) (t : SourceSliceComponentCarrier T component) :
    (g • t).1 = g • t.1 :=
  rfl

noncomputable instance : TopologicalSpace
    (SourceSliceComponentCarrier T component) := ⊥

instance : DiscreteTopology (SourceSliceComponentCarrier T component) :=
  ⟨rfl⟩

end SourceSliceComponentCarrier

/-- The continuous action on the inverse image of one orbit. -/
noncomputable def sourceSliceComponentAction
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) (T : Over S) :
    ContAction FintypeCat.{u} G := by
  refine
    ⟨Action.FintypeCat.ofMulAction G
      (FintypeCat.of (SourceSliceComponentCarrier T component)), ?_⟩
  change ContinuousSMul G (SourceSliceComponentCarrier T component)
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro t
  haveI : ContinuousSMul G T.left.obj.V := T.left.property
  have hopen :
      IsOpen (MulAction.stabilizer G t.1 : Set G) :=
    stabilizer_isOpen G t.1
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer G t.1)
    (H₂ := MulAction.stabilizer G t) _ hopen
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  apply Subtype.ext
  exact hg

/-- The structure map from an orbitwise inverse image to its orbit. -/
noncomputable def sourceSliceComponentHom
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) (T : Over S) :
    sourceSliceComponentAction G S component T ⟶
      sourceActionComponentAction G S component :=
  ObjectProperty.homMk
    ({ hom :=
        FintypeCat.homMk
          (fun t : SourceSliceComponentCarrier T component =>
            (⟨T.hom.hom.hom t.1, t.2⟩ :
              SourceActionComponentFiber G S component))
       comm := fun g => by
         ext t
         apply Subtype.ext
         exact ConcreteCategory.congr_hom (T.hom.hom.comm g) t.1 } :
      (sourceSliceComponentAction G S component T).obj ⟶
        (sourceActionComponentAction G S component).obj)

/-- Restriction of `T -> S` to one orbit, as an object in the orbit slice. -/
noncomputable def sourceSliceComponentObject
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) (T : Over S) :
    Over (sourceActionComponentAction G S component) :=
  Over.mk (sourceSliceComponentHom G S component T)

/-- A slice morphism restricts to every orbit. -/
noncomputable def sourceSliceComponentMap
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S)
    {T U : Over S} (f : T ⟶ U) :
    sourceSliceComponentObject G S component T ⟶
      sourceSliceComponentObject G S component U := by
  let restricted :
      sourceSliceComponentAction G S component T ⟶
        sourceSliceComponentAction G S component U :=
    ObjectProperty.homMk
      ({ hom :=
          FintypeCat.homMk
            (fun t : SourceSliceComponentCarrier T component =>
              (⟨f.left.hom.hom t.1, by
                have hw :=
                  ConcreteCategory.congr_hom
                    (congrArg
                      (fun map : T.left ⟶ S =>
                        (continuousActionFiber G).map map)
                      (Over.w f))
                    t.1
                dsimp only at hw
                rw [Functor.map_comp] at hw
                have hbase :
                    U.hom.hom.hom (f.left.hom.hom t.1) =
                      T.hom.hom.hom t.1 := by
                  simpa only [FintypeCat.comp_apply] using hw
                exact
                  (congrArg
                    (fun s : S.obj.V =>
                      (Quotient.mk'' s : SourceActionComponent G S))
                    hbase).trans t.2⟩ :
                SourceSliceComponentCarrier U component))
         comm := fun g => by
           ext t
           apply Subtype.ext
           exact ConcreteCategory.congr_hom
             (f.left.hom.comm g) t.1 } :
        (sourceSliceComponentAction G S component T).obj ⟶
          (sourceSliceComponentAction G S component U).obj)
  exact Over.homMk restricted (by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext t
    apply Subtype.ext
    have hw :=
      ConcreteCategory.congr_hom
        (congrArg
          (fun map : T.left ⟶ S =>
            (continuousActionFiber G).map map)
          (Over.w f))
        t.1
    dsimp only at hw
    rw [Functor.map_comp] at hw
    exact hw)

/-- Restriction to one orbit as a functor between slice categories. -/
noncomputable def sourceSliceComponentFunctor
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    Over S ⥤ Over (sourceActionComponentAction G S component) where
  obj := sourceSliceComponentObject G S component
  map := sourceSliceComponentMap G S component
  map_id T := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext t
    apply Subtype.ext
    change (𝟙 T.left : T.left ⟶ T.left).hom.hom t.1 = t.1
    exact FintypeCat.id_apply T.left.obj.V t.1
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext t
    apply Subtype.ext
    change
      (f.left ≫ g.left).hom.hom t.1 =
        g.left.hom.hom (f.left.hom.hom t.1)
    exact sourceContinuousAction_comp_apply f.left g.left t.1

/-- Restriction to all orbits.  This is the forward functor in the component
product decomposition of `B(G)_S`. -/
noncomputable def sourceSliceComponentsFunctor
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :
    Over S ⥤
      (∀ component : SourceActionComponent G S,
        Over (sourceActionComponentAction G S component)) :=
  Functor.pi'
    (fun component => sourceSliceComponentFunctor G S component)

/-! ## Gluing a family of orbit-slice objects -/

/-- A family of objects, one over every orbit of `S`. -/
noncomputable abbrev SourceSliceComponentFamily
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :=
  ∀ component : SourceActionComponent G S,
    Over (sourceActionComponentAction G S component)

/-- The disjoint union of the total spaces in a component family. -/
noncomputable abbrev SourceSliceComponentFamilyCarrier
    {G : ProfiniteGrp.{u}} {S : ContAction FintypeCat.{u} G}
    (family : SourceSliceComponentFamily G S) :=
  Σ component : SourceActionComponent G S,
    (family component).left.obj.V

namespace SourceSliceComponentFamilyCarrier

variable
    {G : ProfiniteGrp.{u}}
    {S : ContAction FintypeCat.{u} G}
    (family : SourceSliceComponentFamily G S)

noncomputable instance : Fintype
    (SourceSliceComponentFamilyCarrier family) :=
  Fintype.ofFinite _

noncomputable instance : SMul G
    (SourceSliceComponentFamilyCarrier family) where
  smul g point := ⟨point.1, g • point.2⟩

noncomputable instance : MulAction G
    (SourceSliceComponentFamilyCarrier family) where
  one_smul point := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (one_smul G point.2)
  mul_smul first second point := by
    apply Sigma.ext
    · rfl
    · exact heq_of_eq (mul_smul first second point.2)

@[simp]
theorem smul_fst
    (g : G) (point : SourceSliceComponentFamilyCarrier family) :
    (g • point).1 = point.1 :=
  rfl

@[simp]
theorem smul_snd
    (g : G) (point : SourceSliceComponentFamilyCarrier family) :
    (g • point).2 = g • point.2 :=
  rfl

noncomputable instance : TopologicalSpace
    (SourceSliceComponentFamilyCarrier family) := ⊥

instance : DiscreteTopology
    (SourceSliceComponentFamilyCarrier family) :=
  ⟨rfl⟩

end SourceSliceComponentFamilyCarrier

/-- The continuous action on the disjoint union of a component family. -/
noncomputable def sourceSliceComponentFamilyAction
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S) :
    ContAction FintypeCat.{u} G := by
  refine
    ⟨Action.FintypeCat.ofMulAction G
      (FintypeCat.of (SourceSliceComponentFamilyCarrier family)), ?_⟩
  change ContinuousSMul G (SourceSliceComponentFamilyCarrier family)
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro point
  haveI : ContinuousSMul G (family point.1).left.obj.V :=
    (family point.1).left.property
  have hopen :
      IsOpen
        (MulAction.stabilizer G point.2 : Set G) :=
    stabilizer_isOpen G point.2
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer G point.2)
    (H₂ := MulAction.stabilizer G point) _ hopen
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  apply Sigma.ext
  · rfl
  · exact heq_of_eq hg

/-- The map from the glued total action to `S`, obtained componentwise from
the structure maps and orbit inclusions. -/
noncomputable def sourceSliceComponentFamilyHom
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S) :
    sourceSliceComponentFamilyAction G S family ⟶ S :=
  ObjectProperty.homMk
    ({ hom :=
        FintypeCat.homMk
          (fun point : SourceSliceComponentFamilyCarrier family =>
            ((family point.1).hom.hom.hom point.2).1)
       comm := fun g => by
         ext point
         have hequivariant :=
           ConcreteCategory.congr_hom
             ((family point.1).hom.hom.comm g) point.2
         exact congrArg Subtype.val hequivariant } :
      (sourceSliceComponentFamilyAction G S family).obj ⟶ S.obj)

/-- Glue a family of orbit-slice objects into one object over `S`. -/
noncomputable def sourceSliceComponentFamilyObject
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S) :
    Over S :=
  Over.mk (sourceSliceComponentFamilyHom G S family)

/-- A pointwise morphism of component families glues to a morphism over `S`. -/
noncomputable def sourceSliceComponentFamilyMap
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    {first second : SourceSliceComponentFamily G S}
    (f : first ⟶ second) :
    sourceSliceComponentFamilyObject G S first ⟶
      sourceSliceComponentFamilyObject G S second := by
  let glued :
      sourceSliceComponentFamilyAction G S first ⟶
        sourceSliceComponentFamilyAction G S second :=
    ObjectProperty.homMk
      ({ hom :=
          FintypeCat.homMk
            (fun point : SourceSliceComponentFamilyCarrier first =>
              (⟨point.1,
                (f point.1).left.hom.hom point.2⟩ :
                SourceSliceComponentFamilyCarrier second))
         comm := fun g => by
           ext point
           apply Sigma.ext
           · rfl
           · apply heq_of_eq
             simpa only [FintypeCat.comp_apply] using
               ConcreteCategory.congr_hom
                 ((f point.1).left.hom.comm g) point.2 } :
        (sourceSliceComponentFamilyAction G S first).obj ⟶
          (sourceSliceComponentFamilyAction G S second).obj)
  exact Over.homMk glued (by
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext point
    have hw :=
      ConcreteCategory.congr_hom
        (congrArg
          (fun map :
              (first point.1).left ⟶
                sourceActionComponentAction G S point.1 =>
            (continuousActionFiber G).map map)
          (Over.w (f point.1)))
        point.2
    dsimp only at hw
    rw [Functor.map_comp] at hw
    exact congrArg Subtype.val hw)

/-- Gluing as a functor from the product of component slices. -/
noncomputable def sourceSliceComponentFamilyFunctor
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :
    SourceSliceComponentFamily G S ⥤ Over S where
  obj := sourceSliceComponentFamilyObject G S
  map := sourceSliceComponentFamilyMap G S
  map_id family := by
    dsimp only [sourceSliceComponentFamilyMap]
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext point
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      change
        (𝟙 (family point.1).left :
          (family point.1).left ⟶
            (family point.1).left).hom.hom point.2 =
          point.2
      exact
        FintypeCat.id_apply
          (family point.1).left.obj.V point.2
  map_comp f g := by
    dsimp only [sourceSliceComponentFamilyMap]
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply Action.Hom.ext
    ext point
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      change
        ((f point.1).left ≫ (g point.1).left).hom.hom point.2 =
          (g point.1).left.hom.hom
            ((f point.1).left.hom.hom point.2)
      exact sourceContinuousAction_comp_apply
        (f point.1).left (g point.1).left point.2

/-! ## Gluing after restriction -/

/-- The disjoint union of all orbitwise inverse images of `T -> S` is its
original total space. -/
noncomputable def sourceSliceComponentCarrierSigmaEquiv
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (T : Over S) :
    SourceSliceComponentFamilyCarrier
        ((sourceSliceComponentsFunctor G S).obj T) ≃
      T.left.obj.V :=
  Equiv.sigmaFiberEquiv
    (fun t : T.left.obj.V =>
      (Quotient.mk'' (T.hom.hom.hom t) :
        SourceActionComponent G S))

@[simp]
theorem sourceSliceComponentCarrierSigmaEquiv_apply
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (T : Over S)
    (point : SourceSliceComponentFamilyCarrier
      ((sourceSliceComponentsFunctor G S).obj T)) :
    sourceSliceComponentCarrierSigmaEquiv G S T point =
      point.2.1 :=
  rfl

/-- The reconstruction equivalence is `G`-equivariant. -/
theorem sourceSliceComponentCarrierSigmaEquiv_smul
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (T : Over S) (g : G)
    (point : SourceSliceComponentFamilyCarrier
      ((sourceSliceComponentsFunctor G S).obj T)) :
    sourceSliceComponentCarrierSigmaEquiv G S T (g • point) =
      g • sourceSliceComponentCarrierSigmaEquiv G S T point :=
  rfl

/-- Restricting to all orbits and gluing gives back the original continuous
action. -/
noncomputable def sourceSliceComponentCarrierSigmaActionIso
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (T : Over S) :
    ((sourceSliceComponentsFunctor G S ⋙
        sourceSliceComponentFamilyFunctor G S).obj T).left ≅
      T.left := by
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ ?_
  · change
      FintypeCat.of
          (SourceSliceComponentFamilyCarrier
            ((sourceSliceComponentsFunctor G S).obj T)) ≅
        T.left.obj.V
    exact FintypeCat.equivEquivIso
      (sourceSliceComponentCarrierSigmaEquiv G S T)
  · intro g
    ext point
    exact sourceSliceComponentCarrierSigmaEquiv_smul G S T g point

/-- The preceding action isomorphism commutes with the maps to `S`. -/
noncomputable def sourceSliceComponentCarrierSigmaOverIso
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (T : Over S) :
    (sourceSliceComponentsFunctor G S ⋙
        sourceSliceComponentFamilyFunctor G S).obj T ≅
      T := by
  refine Over.isoMk
    (sourceSliceComponentCarrierSigmaActionIso G S T) ?_
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext point
  rfl

/-- Naturality of reconstruction from orbitwise inverse images. -/
theorem sourceSliceComponentCarrierSigmaOverIso_naturality
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    {T U : Over S} (f : T ⟶ U) :
    (sourceSliceComponentsFunctor G S ⋙
        sourceSliceComponentFamilyFunctor G S).map f ≫
          (sourceSliceComponentCarrierSigmaOverIso G S U).hom =
      (sourceSliceComponentCarrierSigmaOverIso G S T).hom ≫ f := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext point
  dsimp only [
    sourceSliceComponentCarrierSigmaOverIso,
    sourceSliceComponentCarrierSigmaActionIso,
    sourceSliceComponentFamilyFunctor,
    sourceSliceComponentFamilyMap,
    sourceSliceComponentsFunctor,
    sourceSliceComponentFunctor,
    sourceSliceComponentMap]
  change f.left.hom.hom point.2.1 = f.left.hom.hom point.2.1
  rfl

/-- The natural isomorphism `glue (restrict T) ≅ T`. -/
noncomputable def sourceSliceComponentsGlueNatIso
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :
    sourceSliceComponentsFunctor G S ⋙
        sourceSliceComponentFamilyFunctor G S ≅
      𝟭 (Over S) :=
  NatIso.ofComponents
    (sourceSliceComponentCarrierSigmaOverIso G S)
    (fun f =>
      sourceSliceComponentCarrierSigmaOverIso_naturality G S f)

/-! ## Restriction after gluing -/

/-- A point of the `component`-part of a glued family necessarily came from
that same component.  This is the point where the two quotient witnesses are
compared, rather than treating component labels as inert metadata. -/
theorem sourceSliceSplitGluedComponent_index_eq
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S)
    (component : SourceActionComponent G S)
    (point : SourceSliceComponentCarrier
      (sourceSliceComponentFamilyObject G S family) component) :
    point.1.1 = component := by
  have hsource :
      (Quotient.mk''
          (((family point.1.1).hom.hom.hom point.1.2).1) :
        SourceActionComponent G S) =
        point.1.1 :=
    ((family point.1.1).hom.hom.hom point.1.2).2
  have htarget :
      (Quotient.mk''
          (((family point.1.1).hom.hom.hom point.1.2).1) :
        SourceActionComponent G S) =
        component := by
    exact point.2
  exact hsource.symm.trans htarget

/-- Recover the original point in one member of a component family after
gluing and restricting. -/
noncomputable def sourceSliceSplitGluedComponentToFamily
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S)
    (component : SourceActionComponent G S)
    (point : SourceSliceComponentCarrier
      (sourceSliceComponentFamilyObject G S family) component) :
    (family component).left.obj.V :=
  cast
    (congrArg
      (fun index : SourceActionComponent G S =>
        (family index).left.obj.V.obj)
      (sourceSliceSplitGluedComponent_index_eq
        G S family component point))
    point.1.2

/-- Insert a point of one component into the glued family and record that its
image lies in the required orbit. -/
noncomputable def sourceSliceFamilyToSplitGluedComponent
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S)
    (component : SourceActionComponent G S)
    (point : (family component).left.obj.V) :
    SourceSliceComponentCarrier
      (sourceSliceComponentFamilyObject G S family) component :=
  ⟨⟨component, point⟩,
    ((family component).hom.hom.hom point).2⟩

/-- Recovering a point immediately after inserting it is the identity. -/
@[simp]
theorem sourceSliceSplitGluedComponentToFamily_fromFamily
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S)
    (component : SourceActionComponent G S)
    (point : (family component).left.obj.V) :
    sourceSliceSplitGluedComponentToFamily G S family component
        (sourceSliceFamilyToSplitGluedComponent
          G S family component point) =
      point := by
  simp only [
    sourceSliceSplitGluedComponentToFamily,
    sourceSliceFamilyToSplitGluedComponent]
  exact cast_eq _ point

/-- Inserting a recovered point preserves the original dependent component
index and its orbit witness. -/
@[simp]
theorem sourceSliceFamilyToSplitGluedComponent_toFamily
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S)
    (component : SourceActionComponent G S)
    (point : SourceSliceComponentCarrier
      (sourceSliceComponentFamilyObject G S family) component) :
    sourceSliceFamilyToSplitGluedComponent G S family component
        (sourceSliceSplitGluedComponentToFamily
          G S family component point) =
      point := by
  rcases point with ⟨⟨index, point⟩, hcomponent⟩
  have hindex :
      index = component :=
    sourceSliceSplitGluedComponent_index_eq G S family component
      ⟨⟨index, point⟩, hcomponent⟩
  cases hindex
  apply Subtype.ext
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    simp only [
      sourceSliceSplitGluedComponentToFamily,
      sourceSliceFamilyToSplitGluedComponent]
    exact cast_eq _ point

/-- The carrier of one component obtained after gluing is equivalent to the
carrier of the original family member. -/
noncomputable def sourceSliceSplitGluedComponentEquiv
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S)
    (component : SourceActionComponent G S) :
    SourceSliceComponentCarrier
        (sourceSliceComponentFamilyObject G S family) component ≃
      (family component).left.obj.V where
  toFun :=
    sourceSliceSplitGluedComponentToFamily G S family component
  invFun :=
    sourceSliceFamilyToSplitGluedComponent G S family component
  left_inv :=
    sourceSliceFamilyToSplitGluedComponent_toFamily
      G S family component
  right_inv :=
    sourceSliceSplitGluedComponentToFamily_fromFamily
      G S family component

/-- Insertion into a glued component is equivariant. -/
theorem sourceSliceFamilyToSplitGluedComponent_smul
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S)
    (component : SourceActionComponent G S)
    (g : G) (point : (family component).left.obj.V) :
    sourceSliceFamilyToSplitGluedComponent G S family component
        (g • point) =
      g • sourceSliceFamilyToSplitGluedComponent
        G S family component point := by
  apply Subtype.ext
  apply Sigma.ext
  · rfl
  · exact heq_of_eq rfl

/-- Recovery from a glued component is equivariant. -/
theorem sourceSliceSplitGluedComponentEquiv_smul
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S)
    (component : SourceActionComponent G S)
    (g : G)
    (point : SourceSliceComponentCarrier
      (sourceSliceComponentFamilyObject G S family) component) :
    sourceSliceSplitGluedComponentEquiv G S family component
        (g • point) =
      g • sourceSliceSplitGluedComponentEquiv
        G S family component point := by
  apply
    (sourceSliceSplitGluedComponentEquiv G S family component).symm.injective
  rw [Equiv.symm_apply_apply]
  change
    g • point =
      sourceSliceFamilyToSplitGluedComponent G S family component
        (g •
          sourceSliceSplitGluedComponentEquiv
            G S family component point)
  rw [sourceSliceFamilyToSplitGluedComponent_smul]
  exact congrArg (fun value => g • value)
    (sourceSliceFamilyToSplitGluedComponent_toFamily
      G S family component point).symm

/-- Restriction after gluing recovers one family member as a continuous
`G`-action. -/
noncomputable def sourceSliceSplitGluedComponentActionIso
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S)
    (component : SourceActionComponent G S) :
    ((sourceSliceComponentFamilyFunctor G S ⋙
        sourceSliceComponentsFunctor G S).obj family component).left ≅
      (family component).left := by
  apply ObjectProperty.isoMk
  refine Action.mkIso ?_ ?_
  · change
      FintypeCat.of
          (SourceSliceComponentCarrier
            (sourceSliceComponentFamilyObject G S family) component) ≅
        (family component).left.obj.V
    exact FintypeCat.equivEquivIso
      (sourceSliceSplitGluedComponentEquiv G S family component)
  · intro g
    ext point
    exact
      sourceSliceSplitGluedComponentEquiv_smul
        G S family component g point

/-- The recovered component action isomorphism commutes with its map to the
orbit action. -/
theorem sourceSliceSplitGluedComponentActionIso_hom_comp
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S)
    (component : SourceActionComponent G S) :
    (sourceSliceSplitGluedComponentActionIso
          G S family component).hom ≫
        (family component).hom =
      ((sourceSliceComponentFamilyFunctor G S ⋙
        sourceSliceComponentsFunctor G S).obj family component).hom := by
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext point
  rcases point with ⟨⟨index, point⟩, hcomponent⟩
  have hindex :
      index = component :=
    sourceSliceSplitGluedComponent_index_eq G S family component
      ⟨⟨index, point⟩, hcomponent⟩
  cases hindex
  apply Subtype.ext
  change
    ((family component).hom.hom.hom
        (sourceSliceSplitGluedComponentToFamily
          G S family component
            ⟨⟨component, point⟩, hcomponent⟩)).1 =
      ((family component).hom.hom.hom point).1
  congr 1

/-- Restriction after gluing recovers one family member in the corresponding
slice category. -/
noncomputable def sourceSliceSplitGluedComponentOverIso
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S)
    (component : SourceActionComponent G S) :
    (sourceSliceComponentFamilyFunctor G S ⋙
        sourceSliceComponentsFunctor G S).obj family component ≅
      family component :=
  Over.isoMk
    (sourceSliceSplitGluedComponentActionIso G S family component)
    (sourceSliceSplitGluedComponentActionIso_hom_comp
      G S family component)

/-- The pointwise component isomorphisms form an isomorphism of dependent
families. -/
noncomputable def sourceSliceSplitGluedFamilyIso
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (family : SourceSliceComponentFamily G S) :
    (sourceSliceComponentFamilyFunctor G S ⋙
        sourceSliceComponentsFunctor G S).obj family ≅
      family :=
  Pi.isoMk
    (fun component =>
      sourceSliceSplitGluedComponentOverIso
        G S family component)

/-- Naturality of the componentwise recovery isomorphism. -/
theorem sourceSliceSplitGluedFamilyIso_naturality
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    {first second : SourceSliceComponentFamily G S}
    (f : first ⟶ second) :
    (sourceSliceComponentFamilyFunctor G S ⋙
        sourceSliceComponentsFunctor G S).map f ≫
          (sourceSliceSplitGluedFamilyIso G S second).hom =
      (sourceSliceSplitGluedFamilyIso G S first).hom ≫ f := by
  apply Pi.ext
  intro component
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  ext point
  rcases point with ⟨⟨index, point⟩, hcomponent⟩
  have hindex :
      index = component :=
    sourceSliceSplitGluedComponent_index_eq G S first component
      ⟨⟨index, point⟩, hcomponent⟩
  cases hindex
  dsimp only [
    sourceSliceSplitGluedFamilyIso,
    sourceSliceSplitGluedComponentOverIso,
    sourceSliceSplitGluedComponentActionIso,
    sourceSliceComponentsFunctor,
    sourceSliceComponentFunctor,
    sourceSliceComponentMap,
    sourceSliceComponentFamilyFunctor,
    sourceSliceComponentFamilyMap]
  change
    sourceSliceSplitGluedComponentToFamily
        G S second component
        ⟨⟨component, (f component).left.hom.hom point⟩,
          ((second component).hom.hom.hom
            ((f component).left.hom.hom point)).2⟩ =
      (f component).left.hom.hom
        (sourceSliceSplitGluedComponentToFamily
          G S first component
          ⟨⟨component, point⟩, hcomponent⟩)
  simp only [sourceSliceSplitGluedComponentToFamily]
  rw [cast_eq, cast_eq]

/-- Restriction after gluing is naturally isomorphic to the identity on the
product of orbit slices. -/
noncomputable def sourceSliceComponentsSplitNatIso
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :
    sourceSliceComponentFamilyFunctor G S ⋙
        sourceSliceComponentsFunctor G S ≅
      𝟭 (SourceSliceComponentFamily G S) :=
  NatIso.ofComponents
    (sourceSliceSplitGluedFamilyIso G S)
    (fun f =>
      sourceSliceSplitGluedFamilyIso_naturality G S f)

/-- Proposition 1.2.1(i), at the component-product stage: the slice over an
arbitrary finite continuous `G`-set is equivalent to the dependent product of
the slices over its orbit actions. -/
noncomputable def sourceSliceComponentProductEquivalence
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :
    Over S ≌ SourceSliceComponentFamily G S :=
  CategoryTheory.Equivalence.mk
    (sourceSliceComponentsFunctor G S)
    (sourceSliceComponentFamilyFunctor G S)
    (sourceSliceComponentsGlueNatIso G S).symm
    (sourceSliceComponentsSplitNatIso G S)

/-! ## Connected stabilizer factors -/

/-- Transporting along the component/coset action isomorphism identifies the
corresponding slice categories. -/
noncomputable def sourceActionComponentSliceCosetEquivalence
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    Over (sourceActionComponentAction G S component) ≌
      Over (sourceOpenCosetAction G
        (sourceActionComponentOpenStabilizer G S component)) :=
  Over.mapIso
    (sourceActionComponentCosetActionIso G S component)

/-- One orbit factor is the connected anabelioid of the open stabilizer of
the canonical orbit representative. -/
noncomputable def sourceActionComponentConnectedFactorEquivalence
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    Over (sourceActionComponentAction G S component) ≌
      ContAction FintypeCat.{u}
        (sourceActionComponentOpenStabilizer G S component) :=
  (sourceActionComponentSliceCosetEquivalence
      G S component).trans
    (sourceOpenCosetSliceEquivalence G
      (sourceActionComponentOpenStabilizer
        G S component)).symm

/-- The product of orbit slices is equivalent to the product of the connected
anabelioids of the canonical open stabilizers. -/
noncomputable def sourceSliceConnectedFactorsEquivalence
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :
    SourceSliceComponentFamily G S ≌
      (∀ component : SourceActionComponent G S,
        ContAction FintypeCat.{u}
          (sourceActionComponentOpenStabilizer G S component)) :=
  CategoryTheory.Equivalence.pi
    (fun component =>
      sourceActionComponentConnectedFactorEquivalence
        G S component)

/-- Proposition 1.2.1(i) of *The Geometry of Anabelioids* for `B(G)`: the
slice over an arbitrary finite continuous action is a finite product of
connected anabelioids, naturally indexed by the orbit components of `S`. -/
noncomputable def sourceSliceAnabelioidEquivalence
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :
    Over S ≌
      (∀ component : SourceActionComponent G S,
        ContAction FintypeCat.{u}
          (sourceActionComponentOpenStabilizer G S component)) :=
  (sourceSliceComponentProductEquivalence G S).trans
    (sourceSliceConnectedFactorsEquivalence G S)

/-- The connected Galois-category certificate attached to one stabilizer
factor of the slice decomposition. -/
noncomputable def sourceActionComponentEtaleFundamentalGroup
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    EtaleFundamentalGroup.{u} :=
  continuousActionEtaleFundamentalGroup
    (sourceActionComponentStabilizerProfiniteGroup
      G S component)

/-- The certified cover category of a stabilizer factor is definitionally its
category of finite continuous actions. -/
theorem sourceActionComponentEtaleFundamentalGroup_cover_eq
    (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : SourceActionComponent G S) :
    (sourceActionComponentEtaleFundamentalGroup
        G S component).Cover =
      ContAction FintypeCat.{u}
        (sourceActionComponentOpenStabilizer G S component) :=
  rfl

end Iut
