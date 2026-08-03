/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.CategoryTheory.Galois.GaloisObjects
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Category.FinTopCat
import Iut.Foundations.SourceAnabelioid

/-!
# Finite continuous actions as an anabelioid

For a profinite group `G`, Mochizuki's *The Geometry of Anabelioids*,
§1.1, writes `B(G)` for the category of finite discrete sets equipped with a
continuous `G`-action.  The first step in constructing `B(G)` as an actual
Galois category is to prove that continuity is preserved by the finite
categorical operations used in the Galois axioms.

The proofs below do not replace continuous actions by unrestricted finite
actions.  They use the source characterization of continuity: for a discrete
`G`-set, every point stabilizer is open.  A stabilizer in a finite limit
contains the finite intersection of the projected stabilizers, and every
point of a finite colimit is represented by a point of one of the diagram
objects.
-/

namespace Iut

universe u v w

open CategoryTheory
open CategoryTheory.Limits
open scoped FintypeCatDiscrete

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The object property cutting out continuous actions on finite discrete
sets. -/
abbrev continuousFiniteAction :
    ObjectProperty (Action FintypeCat.{u} G) :=
  Action.IsContinuous (V := FintypeCat.{u}) (G := G)

/-- The full inclusion of continuous finite actions into all finite actions. -/
abbrev continuousActionInclusion :
    ContAction FintypeCat.{u} G ⥤ Action FintypeCat.{u} G :=
  ObjectProperty.ι (continuousFiniteAction G)

/-- Continuous finite `G`-actions are closed under limits indexed by a finite
category. -/
noncomputable instance continuousAction_isClosedUnderLimitsOfShape
    (J : Type v) [SmallCategory J] [FinCategory J] :
    (continuousFiniteAction G).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := by
    rintro X ⟨presentation⟩
    change ContinuousSMul G X.V
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    let U : Subgroup G :=
      ⨅ j : J, MulAction.stabilizer G ((presentation.π.app j).hom x)
    have hU_open : IsOpen (U : Set G) := by
      rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun j => by
        haveI : ContinuousSMul G (presentation.diag.obj j).V :=
          presentation.prop_diag_obj j
        exact stabilizer_isOpen G _
    apply Subgroup.isOpen_mono (H₁ := U) (H₂ := MulAction.stabilizer G x) _ hU_open
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Concrete.isLimit_ext presentation.diag presentation.isLimit
    intro j
    have hgj :
        g ∈ MulAction.stabilizer G ((presentation.π.app j).hom x) :=
      Subgroup.mem_iInf.mp hg j
    have hfix :
        g • (presentation.π.app j).hom x =
          (presentation.π.app j).hom x :=
      MulAction.mem_stabilizer_iff.mp hgj
    have hequivariant :=
      ConcreteCategory.congr_hom ((presentation.π.app j).comm g) x
    exact hequivariant.trans hfix

/-- A colimit of continuous finite actions is continuous whenever the two
underlying forgetful functors preserve that particular colimit. -/
private theorem continuousFiniteAction_of_isColimit
    {J : Type v} [Category.{w} J] {X : Action FintypeCat.{u} G}
    (presentation : (continuousFiniteAction G).ColimitOfShape J X)
    [PreservesColimit presentation.diag (Action.forget FintypeCat G)]
    [PreservesColimit
      (presentation.diag ⋙ Action.forget FintypeCat G)
      FintypeCat.incl] :
    continuousFiniteAction G X := by
  change ContinuousSMul G X.V
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  let mappedCocone :=
    (Action.forget FintypeCat G).mapCocone presentation.cocone
  have mappedIsColimit : IsColimit mappedCocone :=
    isColimitOfPreserves (Action.forget FintypeCat G) presentation.isColimit
  let typeCocone := FintypeCat.incl.mapCocone mappedCocone
  have typeIsColimit : IsColimit typeCocone :=
    isColimitOfPreserves FintypeCat.incl mappedIsColimit
  obtain ⟨j, (y : (presentation.diag.obj j).V), hy⟩ :=
    Types.jointly_surjective
      (presentation.diag ⋙ Action.forget FintypeCat G ⋙
        FintypeCat.incl)
      typeIsColimit x
  have hy_open :
      IsOpen
        (MulAction.stabilizer G y : Set G) :=
    by
      haveI : ContinuousSMul G (presentation.diag.obj j).V :=
        presentation.prop_diag_obj j
      exact stabilizer_isOpen G y
  apply Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer G y)
    (H₂ := MulAction.stabilizer G x) _ hy_open
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [← hy]
  have hequivariant :=
    ConcreteCategory.congr_hom ((presentation.ι.app j).comm g) y
  exact hequivariant.symm.trans (congrArg (presentation.ι.app j).hom hg)

/-- Continuous finite `G`-actions are closed under colimits indexed by a
small finite category. -/
noncomputable instance continuousAction_isClosedUnderColimitsOfShape
    (J : Type v) [SmallCategory J] [FinCategory J] :
    (continuousFiniteAction G).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨presentation⟩
    exact continuousFiniteAction_of_isColimit G presentation

/-- Quotients by an arbitrary-universe finite group remain continuous.  This
separate instance covers `SingleObj Q`, whose object and morphism universes
need not agree. -/
noncomputable instance continuousAction_isClosedUnderFiniteGroupQuotients
    (Q : Type v) [Group Q] [Finite Q] :
    (continuousFiniteAction G).IsClosedUnderColimitsOfShape
      (SingleObj Q) where
  colimitsOfShape_le := by
    rintro X ⟨presentation⟩
    exact continuousFiniteAction_of_isColimit G presentation

noncomputable instance continuousActionInclusion_createsFiniteLimits :
    CreatesFiniteLimits (continuousActionInclusion G) where
  createsFiniteLimits J _ _ := by
    letI :
        (continuousFiniteAction G).IsClosedUnderLimitsOfShape J :=
      continuousAction_isClosedUnderLimitsOfShape G J
    infer_instance

noncomputable instance continuousActionInclusion_createsFiniteColimits :
    CreatesFiniteColimits (continuousActionInclusion G) where
  createsFiniteColimits J _ _ := by
    letI :
        (continuousFiniteAction G).IsClosedUnderColimitsOfShape J :=
      continuousAction_isClosedUnderColimitsOfShape G J
    infer_instance

noncomputable instance continuousActionInclusion_createsFiniteGroupQuotients
    (Q : Type v) [Group Q] [Finite Q] :
    CreatesColimitsOfShape (SingleObj Q) (continuousActionInclusion G) := by
  letI :
      (continuousFiniteAction G).IsClosedUnderColimitsOfShape
        (SingleObj Q) :=
    continuousAction_isClosedUnderFiniteGroupQuotients G Q
  infer_instance

noncomputable instance continuousActionInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (continuousActionInclusion G) := by
  infer_instance

noncomputable instance continuousActionInclusion_preservesFiniteColimits :
    PreservesFiniteColimits (continuousActionInclusion G) := by
  infer_instance

noncomputable instance continuousActionInclusion_preservesFiniteGroupQuotients
    (Q : Type v) [Group Q] [Finite Q] :
    PreservesColimitsOfShape (SingleObj Q) (continuousActionInclusion G) := by
  infer_instance

/-! ## The Galois axioms -/

/-- The complement of the image of a morphism of continuous finite actions,
equipped with the action constructed in `Action.imageComplement`. -/
noncomputable def continuousActionImageComplement
    {X Y : ContAction FintypeCat.{u} G} (f : X ⟶ Y) :
    ContAction FintypeCat.{u} G :=
  ⟨FintypeCat.Action.imageComplement G f.hom, by
    change ContinuousSMul G (FintypeCat.Action.imageComplement G f.hom).V
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro y
    haveI : ContinuousSMul G Y.obj.V := Y.property
    have h_open :
        IsOpen (MulAction.stabilizer G y.val : Set G) :=
      stabilizer_isOpen G y.val
    apply Subgroup.isOpen_mono
      (H₁ := MulAction.stabilizer G y.val)
      (H₂ := MulAction.stabilizer G y) _ h_open
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    apply Subtype.ext
    exact hg⟩

/-- The equivariant inclusion of the complement of the image. -/
noncomputable def continuousActionImageComplementIncl
    {X Y : ContAction FintypeCat.{u} G} (f : X ⟶ Y) :
    continuousActionImageComplement G f ⟶ Y :=
  ObjectProperty.homMk
    (FintypeCat.Action.imageComplementIncl G f.hom)

instance continuousActionImageComplementIncl_mono
    {X Y : ContAction FintypeCat.{u} G} (f : X ⟶ Y) :
    Mono (continuousActionImageComplementIncl G f) := by
  apply Functor.mono_of_mono_map
    (ObjectProperty.ι (continuousFiniteAction G))
  exact inferInstanceAs <| Mono (FintypeCat.Action.imageComplementIncl G f.hom)

/-- Finite continuous `G`-sets satisfy the pre-Galois axioms.  In particular,
the direct-summand complement is the actual invariant complement of the image,
not an abstractly supplied object. -/
noncomputable instance continuousAction_preGaloisCategory :
    PreGaloisCategory (ContAction FintypeCat.{u} G) where
  hasTerminal := inferInstance
  hasPullbacks := inferInstance
  hasFiniteCoproducts := ⟨fun n => by
    letI :
        (continuousFiniteAction G).IsClosedUnderColimitsOfShape
          (Discrete (Fin n)) :=
      continuousAction_isClosedUnderColimitsOfShape G _
    infer_instance⟩
  hasQuotientsByFiniteGroups Q _ _ := by
    letI :
        (continuousFiniteAction G).IsClosedUnderColimitsOfShape
          (SingleObj Q) :=
      continuousAction_isClosedUnderFiniteGroupQuotients G Q
    infer_instance
  monoInducesIsoOnDirectSummand {_ _} i _ := by
    let inclusion :=
      ObjectProperty.ι (continuousFiniteAction G)
    haveI : Mono (inclusion.map i) := Functor.map_mono inclusion i
    refine
      ⟨continuousActionImageComplement G i,
        continuousActionImageComplementIncl G i, ⟨?_⟩⟩
    apply isColimitOfReflects inclusion
    exact
      (isColimitMapCoconeBinaryCofanEquiv inclusion i
        (continuousActionImageComplementIncl G i)).symm <|
        isColimitOfReflects
          (Action.forget FintypeCat G ⋙ FintypeCat.incl) <|
          (isColimitMapCoconeBinaryCofanEquiv
            (Action.forget FintypeCat G ⋙ FintypeCat.incl)
            (inclusion.map i)
            (inclusion.map (continuousActionImageComplementIncl G i))).symm <|
            Types.isCoprodOfMono
              ((Action.forget FintypeCat G ⋙ FintypeCat.incl).map
                (inclusion.map i))

/-! ## The fiber functor -/

/-- The underlying finite-set functor on continuous finite actions. -/
abbrev continuousActionFiber :
    ContAction FintypeCat.{u} G ⥤ FintypeCat.{u} :=
  continuousActionInclusion G ⋙ Action.forget FintypeCat G

/-- The underlying finite-set functor is a fiber functor. -/
noncomputable instance continuousAction_fiberFunctor :
    PreGaloisCategory.FiberFunctor (continuousActionFiber G) where
  preservesFiniteCoproducts := ⟨fun _ => inferInstance⟩
  preservesQuotientsByFiniteGroups _ _ _ := inferInstance
  reflectsIsos := ⟨fun f (_ : IsIso f.hom.hom) => by
    haveI : IsIso f.hom := inferInstance
    exact (ObjectProperty.isIso_hom_iff f).mp inferInstance⟩

/-- The category `B(G)` of finite continuous `G`-sets is a Galois category. -/
noncomputable instance continuousAction_galoisCategory :
    GaloisCategory (ContAction FintypeCat.{u} G) where
  hasFiberFunctor := ⟨continuousActionFiber G, ⟨inferInstance⟩⟩

/-! ## Recovery of the original profinite group -/

instance continuousActionFiber_mulAction
    (X : ContAction FintypeCat.{u} G) :
    MulAction G ((continuousActionFiber G).obj X) :=
  inferInstanceAs <| MulAction G X.obj.V

instance continuousAction_isNaturalSMul :
    PreGaloisCategory.IsNaturalSMul (continuousActionFiber G) G where
  naturality g {_} {_} f x :=
    ConcreteCategory.congr_hom (f.hom.comm g) x

/-- A connected continuous finite action is transitive.  The proof constructs
the orbit as a continuous invariant subobject and invokes connectedness. -/
theorem continuousAction_pretransitive_of_isConnected
    (X : ContAction FintypeCat.{u} G)
    [PreGaloisCategory.IsConnected X] :
    MulAction.IsPretransitive G ((continuousActionFiber G).obj X) where
  exists_smul_eq x y := by
    let T : Set X.obj.V := MulAction.orbit G x
    haveI : Fintype T := Fintype.ofFinite T
    letI : MulAction G (FintypeCat.of T) := inferInstanceAs <| MulAction G T
    let orbitAction : Action FintypeCat G :=
      Action.FintypeCat.ofMulAction G (FintypeCat.of T)
    have orbitContinuous : continuousFiniteAction G orbitAction := by
      change ContinuousSMul G orbitAction.V
      rw [continuousSMul_iff_stabilizer_isOpen]
      intro z
      haveI : ContinuousSMul G X.obj.V := X.property
      have h_open :
          IsOpen (MulAction.stabilizer G z.val : Set G) :=
        stabilizer_isOpen G z.val
      apply Subgroup.isOpen_mono
        (H₁ := MulAction.stabilizer G z.val)
        (H₂ := MulAction.stabilizer G z) _ h_open
      intro g hg
      rw [MulAction.mem_stabilizer_iff] at hg ⊢
      apply Subtype.ext
      exact hg
    let T' : ContAction FintypeCat G :=
      ⟨orbitAction, orbitContinuous⟩
    let i : T' ⟶ X :=
      ObjectProperty.homMk
        ({ hom := FintypeCat.homMk Subtype.val
           comm := fun _ => rfl } : orbitAction ⟶ X.obj)
    haveI : Mono i := by
      apply Functor.mono_of_mono_map (continuousActionInclusion G)
      apply Functor.mono_of_mono_map (Action.forget FintypeCat G)
      apply ConcreteCategory.mono_of_injective
      exact Subtype.val_injective
    haveI : IsIso i := by
      apply PreGaloisCategory.IsConnected.noTrivialComponent T' i
      apply
        (PreGaloisCategory.not_initial_iff_fiber_nonempty
          (continuousActionFiber G) T').mpr
      exact Set.Nonempty.coe_sort (MulAction.nonempty_orbit x)
    have hb :
        Function.Bijective ((continuousActionFiber G).map i) := by
      apply (ConcreteCategory.isIso_iff_bijective _).mp
      exact (continuousActionFiber G).map_isIso i
    obtain ⟨⟨y', ⟨g, (hg : g • x = y')⟩⟩, (hy' : y' = y)⟩ :=
      hb.surjective y
    exact ⟨g, hg.trans hy'⟩

/-- The finite continuous left-translation action on `G/H` for an open normal
subgroup `H`. -/
noncomputable def continuousActionQuotient
    [CompactSpace G] (H : OpenNormalSubgroup G) :
    ContAction FintypeCat.{u} G :=
  letI : TopologicalSpace (G ⧸ H.toSubgroup) := ⊥
  letI : DiscreteTopology (G ⧸ H.toSubgroup) := ⟨rfl⟩
  letI : Fintype (G ⧸ H.toSubgroup) :=
    have : Finite (G ⧸ H.toSubgroup) :=
      H.toSubgroup.quotient_finite_of_isOpen H.isOpen'
    Fintype.ofFinite _
  ⟨G ⧸ₐ H.toSubgroup, by
    change ContinuousSMul G (G ⧸ H.toSubgroup)
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro q
    apply Subgroup.isOpen_mono
      (H₁ := H.toSubgroup)
      (H₂ := MulAction.stabilizer G q) _ H.isOpen'
    intro h hh
    rw [MulAction.mem_stabilizer_iff]
    induction q using QuotientGroup.induction_on with
    | _ a =>
        rw [MulAction.Quotient.smul_mk, QuotientGroup.eq_iff_div_mem]
        simpa using hh⟩

/-- The identity coset in the continuous quotient action. -/
noncomputable def continuousActionQuotientBasepoint
    [CompactSpace G] (H : OpenNormalSubgroup G) :
    (continuousActionFiber G).obj (continuousActionQuotient G H) := by
  change G ⧸ H.toSubgroup
  exact 1

/-- Finite continuous quotient actions separate the points of a profinite
group. -/
theorem continuousAction_nontrivial
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (g : G)
    (hfix :
      ∀ (X : ContAction FintypeCat.{u} G)
        (x : (continuousActionFiber G).obj X), g • x = x) :
    g = 1 := by
  by_contra hne
  obtain ⟨H, hH⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (G := G) (isOpen_compl_singleton)
      (Set.mem_compl_singleton_iff.mpr fun h => hne h.symm)
  have hgfix :=
    hfix (continuousActionQuotient G H)
      (continuousActionQuotientBasepoint G H)
  change
    g • (QuotientGroup.mk (1 : G) : G ⧸ H.toSubgroup) =
      QuotientGroup.mk (1 : G) at hgfix
  rw [MulAction.Quotient.smul_mk] at hgfix
  have hgquot : (g : G ⧸ H.toSubgroup) = 1 := by
    simpa only [smul_eq_mul, mul_one] using hgfix
  have hgH : g ∈ H := by
    change g ∈ H.toSubgroup
    exact (QuotientGroup.eq_one_iff g).mp hgquot
  exact (hH hgH) rfl

/-- The original profinite group is a fundamental group of its category of
finite continuous actions. -/
noncomputable instance continuousAction_isFundamentalGroup
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    PreGaloisCategory.IsFundamentalGroup (continuousActionFiber G) G where
  naturality g {_} {_} f x :=
    ConcreteCategory.congr_hom (f.hom.comm g) x
  transitive_of_isGalois X :=
    continuousAction_pretransitive_of_isConnected G X
  continuous_smul X := X.property
  non_trivial' := continuousAction_nontrivial G

/-! ## The certified anabelioid `B(G)` -/

/-- The connected anabelioid `B(G)` attached to a profinite group `G`, with
its canonical fiber functor and its original group as certified fundamental
group. -/
noncomputable def continuousActionEtaleFundamentalGroup
    (G : ProfiniteGrp.{u}) :
    EtaleFundamentalGroup.{u} where
  Cover := ContAction FintypeCat.{u} G
  coverCategory := inferInstance
  galoisCategory := continuousAction_galoisCategory G
  fiber := continuousActionFiber G
  fiberFunctor := continuousAction_fiberFunctor G
  group := G
  action := continuousActionFiber_mulAction G
  isFundamentalGroup := continuousAction_isFundamentalGroup G

/-! ## Exact restriction functors -/

noncomputable instance actionRes_preservesFiniteLimits
    {H K : Type u} [Group H] [Group K] (f : H →* K) :
    PreservesFiniteLimits (Action.res FintypeCat.{u} f) where
  preservesFiniteLimits J _ _ := by
    apply Action.preservesLimitsOfShape_of_preserves
    change PreservesLimitsOfShape J (Action.forget FintypeCat K)
    infer_instance

noncomputable instance actionRes_preservesFiniteColimits
    {H K : Type u} [Group H] [Group K] (f : H →* K) :
    PreservesFiniteColimits (Action.res FintypeCat.{u} f) where
  preservesFiniteColimits J _ _ := by
    apply Action.preservesColimitsOfShape_of_preserves
    change PreservesColimitsOfShape J (Action.forget FintypeCat K)
    infer_instance

noncomputable instance continuousActionRes_preservesFiniteLimits
    {H K : Type u}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (f : H →ₜ* K) :
    PreservesFiniteLimits (ContAction.res FintypeCat.{u} f) where
  preservesFiniteLimits J _ _ := by
    haveI : PreservesLimitsOfShape J
        (ContAction.res FintypeCat f ⋙ continuousActionInclusion H) := by
      change PreservesLimitsOfShape J
        (continuousActionInclusion K ⋙
          Action.res FintypeCat f.toMonoidHom)
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (ContAction.res FintypeCat f) (continuousActionInclusion H)

noncomputable instance continuousActionRes_preservesFiniteColimits
    {H K : Type u}
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (f : H →ₜ* K) :
    PreservesFiniteColimits (ContAction.res FintypeCat.{u} f) where
  preservesFiniteColimits J _ _ := by
    haveI : PreservesColimitsOfShape J
        (ContAction.res FintypeCat f ⋙ continuousActionInclusion H) := by
      change PreservesColimitsOfShape J
        (continuousActionInclusion K ⋙
          Action.res FintypeCat f.toMonoidHom)
      infer_instance
    exact preservesColimitsOfShape_of_reflects_of_preserves
      (ContAction.res FintypeCat f) (continuousActionInclusion H)

/-- Restriction of finite continuous actions along a morphism of profinite
groups, regarded contravariantly as a pointed exact morphism of anabelioids. -/
noncomputable def continuousActionPointedHom
    {H K : ProfiniteGrp.{u}} (f : H ⟶ K) :
    SourcePointedAnabelioidHom
      (continuousActionEtaleFundamentalGroup H)
      (continuousActionEtaleFundamentalGroup K) := by
  letI := (continuousActionEtaleFundamentalGroup H).coverCategory
  letI := (continuousActionEtaleFundamentalGroup K).coverCategory
  exact
    { pullback := ContAction.res FintypeCat f.hom
      preservesFiniteLimits := continuousActionRes_preservesFiniteLimits f.hom
      preservesFiniteColimits := continuousActionRes_preservesFiniteColimits f.hom
      fiberIso := NatIso.ofComponents (fun _ => Iso.refl _) }

/-- The map on certified fundamental groups induced by restriction is the
original morphism of profinite groups. -/
theorem continuousActionPointedHom_fundamentalGroupHom
    {H K : ProfiniteGrp.{u}} (f : H ⟶ K) (h : H) :
    (continuousActionPointedHom f).fundamentalGroupHom h = f h := by
  let source := continuousActionEtaleFundamentalGroup H
  let target := continuousActionEtaleFundamentalGroup K
  letI := source.coverCategory
  letI := target.coverCategory
  apply (SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv target).injective
  rw [
    SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv_fundamentalGroupHom
      (continuousActionPointedHom f) h]
  ext X x
  rfl

/-! ## The connected finite-etale open-image criterion -/

/-- A pointed exact anabelioid morphism whose derived map on fundamental
groups is an open embedding.  By *The Geometry of Anabelioids*,
Remark 1.2.2.1, this is the group-theoretic characterization of a connected
finite-etale morphism after basepoints are chosen. -/
structure SourceConnectedFiniteEtaleHom
    (source target : EtaleFundamentalGroup.{u}) where
  toPointedHom : SourcePointedAnabelioidHom source target
  fundamentalGroupIsOpenEmbedding :
    Topology.IsOpenEmbedding toPointedHom.fundamentalGroupHom

namespace SourceConnectedFiniteEtaleHom

variable {source target : EtaleFundamentalGroup.{u}}

/-- The derived map of the restriction morphism agrees as a morphism in
`ProfiniteGrp` with the original group map. -/
theorem continuousActionPointedHom_fundamentalGroupHom_eq
    {H K : ProfiniteGrp.{u}} (f : H ⟶ K) :
    (continuousActionPointedHom f).fundamentalGroupHom = f := by
  ext h
  exact continuousActionPointedHom_fundamentalGroupHom f h

/-- An open embedding of profinite groups gives a connected finite-etale
pointed morphism `B(H) → B(K)` by restriction of actions. -/
noncomputable def ofProfiniteOpenEmbedding
    {H K : ProfiniteGrp.{u}} (embedding : ProfiniteOpenEmbedding H K) :
    SourceConnectedFiniteEtaleHom
      (continuousActionEtaleFundamentalGroup H)
      (continuousActionEtaleFundamentalGroup K) where
  toPointedHom := continuousActionPointedHom embedding.hom
  fundamentalGroupIsOpenEmbedding := by
    rw [continuousActionPointedHom_fundamentalGroupHom_eq]
    exact embedding.isOpenEmbedding

theorem ofProfiniteOpenEmbedding_fundamentalGroupHom
    {H K : ProfiniteGrp.{u}} (embedding : ProfiniteOpenEmbedding H K) :
    (ofProfiniteOpenEmbedding embedding).toPointedHom.fundamentalGroupHom =
      embedding.hom :=
  continuousActionPointedHom_fundamentalGroupHom_eq embedding.hom

end SourceConnectedFiniteEtaleHom

end Iut
