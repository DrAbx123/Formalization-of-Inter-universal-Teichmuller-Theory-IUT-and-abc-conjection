/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceConnectedAnabelioidSlice

/-!
# The connected finite-etale converse after choosing basepoints

Remark 1.2.2.1 of Mochizuki's *The Geometry of Anabelioids* states that every
finite-etale morphism of connected anabelioids is induced by the inclusion of
an open subgroup after suitable basepoints are chosen.

The preceding connected-slice classification recovers an open stabilizer
`H ≤ G`, an equivalence of the source with `B(H)`, and a natural isomorphism
between the original pullback and restriction along `H ≤ G`.  This file makes
the paper's basepoint choice: it transports the canonical fiber functor and
the certified fundamental group `H` across the source equivalence.  The
resulting pointed morphism is then proved to induce the actual open inclusion.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

/-! ## Transporting the canonical basepoint across an equivalence -/

namespace SourceEquivalenceBasepoint

variable
    {H : ProfiniteGrp.{u}}
    {D : Type (u + 1)} [Category.{u} D] [GaloisCategory D]

/-- The fiber functor on `D` obtained by transporting the canonical
basepoint of `B(H)` across an equivalence `D ≃ B(H)`. -/
abbrev fiber
    (equivalence : D ≌ ContAction FintypeCat.{u} H) :
    D ⥤ FintypeCat.{u} :=
  equivalence.functor ⋙ continuousActionFiber H

noncomputable instance fiber_fiberFunctor
    (equivalence : D ≌ ContAction FintypeCat.{u} H) :
    FiberFunctor (fiber equivalence) where
  preservesTerminalObjects := inferInstance
  preservesPullbacks := inferInstance
  preservesFiniteCoproducts := inferInstance
  preservesEpis := inferInstance
  preservesQuotientsByFiniteGroups _ := inferInstance
  reflectsIsos := inferInstance

/-- The recovered group acts on the transported fibers through the canonical
action on `B(H)`. -/
instance fiber_mulAction
    (equivalence : D ≌ ContAction FintypeCat.{u} H)
    (X : D) :
    MulAction H ((fiber equivalence).obj X) :=
  continuousActionFiber_mulAction H (equivalence.functor.obj X)

/-- The transported canonical action of `H` is again a certified fundamental
group action. -/
noncomputable instance fiber_isFundamentalGroup
    (equivalence : D ≌ ContAction FintypeCat.{u} H) :
    IsFundamentalGroup (fiber equivalence) H where
  naturality h {_} {_} f x :=
    ConcreteCategory.congr_hom
      ((equivalence.functor.map f).hom.comm h) x
  transitive_of_isGalois X isGalois := by
    letI : IsGalois X := isGalois
    letI : IsConnected X := IsGalois.toIsConnected
    letI : IsConnected (equivalence.functor.obj X) :=
      sourceIsConnected_equivalence_functor equivalence
        (show IsConnected X from inferInstance)
    exact continuousAction_pretransitive_of_isConnected H
      (equivalence.functor.obj X)
  continuous_smul X :=
    (equivalence.functor.obj X).property
  non_trivial' h fixed := by
    apply continuousAction_nontrivial H h
    intro Y y
    let X := equivalence.inverse.obj Y
    let comparison := equivalence.counitIso.app Y
    let x : (fiber equivalence).obj X :=
      comparison.inv.hom.hom y
    have hx : h • x = x := fixed X x
    have comparison_cancel : comparison.hom.hom x = y := by
      exact FintypeCat.inv_hom_id_apply
        ((continuousActionFiber H).mapIso comparison) y
    have equivariance :=
      ConcreteCategory.congr_hom (comparison.hom.hom.comm h) x
    rw [← comparison_cancel]
    exact equivariance.symm.trans (congrArg comparison.hom.hom hx)

/-- The source category equipped with the basepoint selected by an
equivalence with `B(H)` and with certified fundamental group `H`. -/
noncomputable def etaleFundamentalGroup
    (equivalence : D ≌ ContAction FintypeCat.{u} H) :
    EtaleFundamentalGroup.{u} where
  Cover := D
  coverCategory := inferInstance
  galoisCategory := inferInstance
  fiber := fiber equivalence
  fiberFunctor := fiber_fiberFunctor equivalence
  group := H
  action := fiber_mulAction equivalence
  isFundamentalGroup := fiber_isFundamentalGroup equivalence

end SourceEquivalenceBasepoint

namespace SourcePointedAnabelioidHom

/-- The canonical comparison from a certified fundamental group to the
automorphism group of its fiber functor acts by the stored group action. -/
theorem certifiedFundamentalGroupEquiv_hom_app
    (data : EtaleFundamentalGroup.{u}) (g : data.group) :
    letI := data.coverCategory
    letI := data.galoisCategory
    letI := data.fiberFunctor
    letI (X : data.Cover) := data.action X
    ∀ (X : data.Cover) (x : data.fiber.obj X),
      (certifiedFundamentalGroupEquiv data g).hom.app X x =
        g • x := by
  dsimp
  intro X x
  rfl

end SourcePointedAnabelioidHom

/-! ## The basepoint selected by a connected finite-etale factorization -/

namespace SourceFiniteEtaleFunctorFactorization

variable
    {G : ProfiniteGrp.{u}}
    {D : Type (u + 1)} [Category.{u} D] [GaloisCategory D]
    {pullback : ContAction FintypeCat.{u} G ⥤ D}

/-- The open stabilizer recovered from a connected finite-etale factorization,
regarded as an object of `ProfiniteGrp`. -/
noncomputable def connectedObjectProfiniteGroup
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    ProfiniteGrp.{u} := by
  let H := factorization.connectedObjectOpenStabilizer
  letI : IsTopologicalGroup H :=
    Topology.IsInducing.subtypeVal.topologicalGroup H.toSubgroup.subtype
  letI : CompactSpace H :=
    isCompact_iff_compactSpace.mp H.isClosed.isCompact
  exact ProfiniteGrp.of H

/-- The recovered open stabilizer embeds continuously into the ambient
profinite group. -/
noncomputable def connectedObjectProfiniteInclusion
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    factorization.connectedObjectProfiniteGroup ⟶ G := by
  let H := factorization.connectedObjectOpenStabilizer
  letI : IsTopologicalGroup H :=
    Topology.IsInducing.subtypeVal.topologicalGroup H.toSubgroup.subtype
  letI : CompactSpace H :=
    isCompact_iff_compactSpace.mp H.isClosed.isCompact
  exact ProfiniteGrp.ofHom (sourceOpenSubgroupInclusion G H)

/-- The selected source basepoint in Remark 1.2.2.1: transport the canonical
basepoint of `B(H)` back through the derived source equivalence. -/
noncomputable def connectedSourceEtaleFundamentalGroup
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    EtaleFundamentalGroup.{u} := by
  let H := factorization.connectedObjectOpenStabilizer
  letI : IsTopologicalGroup H :=
    Topology.IsInducing.subtypeVal.topologicalGroup H.toSubgroup.subtype
  letI : CompactSpace H :=
    isCompact_iff_compactSpace.mp H.isClosed.isCompact
  exact SourceEquivalenceBasepoint.etaleFundamentalGroup
    (H := ProfiniteGrp.of H) factorization.connectedSourceEquivalence

/-- The original finite-etale pullback equipped with the selected source and
canonical target basepoints. -/
noncomputable def connectedPointedHom
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    SourcePointedAnabelioidHom
      factorization.connectedSourceEtaleFundamentalGroup
      (continuousActionEtaleFundamentalGroup G) := by
  let H := factorization.connectedObjectOpenStabilizer
  letI : IsTopologicalGroup H :=
    Topology.IsInducing.subtypeVal.topologicalGroup H.toSubgroup.subtype
  letI : CompactSpace H :=
    isCompact_iff_compactSpace.mp H.isClosed.isCompact
  let source :=
    factorization.connectedSourceEtaleFundamentalGroup
  let target := continuousActionEtaleFundamentalGroup G
  let equivalence := factorization.connectedSourceEquivalence
  let comparison :=
    factorization.connectedSourcePullbackIsoRestriction
  letI : PreservesFiniteLimits
      (Over.star factorization.object) :=
    sourceSliceProduct_preservesFiniteLimits G factorization.object
  letI : PreservesFiniteColimits
      (Over.star factorization.object) :=
    sourceSliceProduct_preservesFiniteColimits G factorization.object
  letI : PreservesFiniteLimits
      (Over.star factorization.object ⋙
        factorization.sliceEquivalence.inverse) := inferInstance
  letI : PreservesFiniteColimits
      (Over.star factorization.object ⋙
        factorization.sliceEquivalence.inverse) := inferInstance
  let pullbackPreservesFiniteLimits :
      PreservesFiniteLimits pullback :=
    preservesFiniteLimits_of_natIso factorization.pullbackIso.symm
  let pullbackPreservesFiniteColimits :
      PreservesFiniteColimits pullback :=
    preservesFiniteColimits_of_natIso factorization.pullbackIso.symm
  letI := source.coverCategory
  letI := target.coverCategory
  let restrictionPointed :=
    continuousActionPointedHom
      factorization.connectedObjectProfiniteInclusion
  exact
    { pullback := pullback
      preservesFiniteLimits := pullbackPreservesFiniteLimits
      preservesFiniteColimits := pullbackPreservesFiniteColimits
      fiberIso :=
        (Functor.associator
          pullback equivalence.functor (continuousActionFiber H)).symm ≪≫
          Functor.isoWhiskerRight comparison
            (continuousActionFiber H) ≪≫
          restrictionPointed.fiberIso }

/-- With the basepoints selected by the categorical classification, the
fundamental-group homomorphism of the original pullback is the recovered open
subgroup inclusion itself. -/
theorem connectedPointedHom_fundamentalGroupHom
    (factorization : SourceFiniteEtaleFunctorFactorization pullback)
    (h : factorization.connectedSourceEtaleFundamentalGroup.group) :
    factorization.connectedPointedHom.fundamentalGroupHom h =
      factorization.connectedObjectProfiniteInclusion h := by
  let H := factorization.connectedObjectOpenStabilizer
  letI : IsTopologicalGroup H :=
    Topology.IsInducing.subtypeVal.topologicalGroup H.toSubgroup.subtype
  letI : CompactSpace H :=
    isCompact_iff_compactSpace.mp H.isClosed.isCompact
  let source :=
    factorization.connectedSourceEtaleFundamentalGroup
  let target := continuousActionEtaleFundamentalGroup G
  let morphism := factorization.connectedPointedHom
  let inclusion := factorization.connectedObjectProfiniteInclusion
  letI := source.coverCategory
  letI := target.coverCategory
  letI := source.galoisCategory
  letI := target.galoisCategory
  letI := source.fiberFunctor
  letI := target.fiberFunctor
  letI (Y : source.Cover) :
      MulAction source.group (source.fiber.obj Y) :=
    source.action Y
  letI (Y : target.Cover) :
      MulAction target.group (target.fiber.obj Y) :=
    target.action Y
  apply
    (SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv
      target).injective
  rw [
    SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv_fundamentalGroupHom
      morphism]
  ext X x
  letI : SMul target.group (target.fiber.obj X) :=
    (target.action X).toSemigroupAction.toSMul
  let targetElement : target.group := inclusion h
  let automorphism :=
    SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv
      source h
  let point : source.fiber.obj (morphism.pullback.obj X) :=
    morphism.fiberIso.inv.app X x
  have cancellation :
      morphism.fiberIso.hom.app X point = x :=
    FintypeCat.inv_hom_id_apply (morphism.fiberIso.app X) x
  have sourceActs :
      automorphism • point = h • point := by
    exact
      SourcePointedAnabelioidHom.certifiedFundamentalGroupEquiv_hom_app
        source h (morphism.pullback.obj X) point
  have pointedEquivariance :=
    morphism.fiberIso_equivariant automorphism X point
  have inclusionEquivariance :
      morphism.fiberIso.hom.app X (h • point) =
        SMul.smul targetElement
          (morphism.fiberIso.hom.app X point) := by
    let comparison :=
      factorization.connectedSourcePullbackIsoRestriction
    exact
      ConcreteCategory.congr_hom
        ((comparison.hom.app X).hom.comm h) point
  change
    (morphism.fiberAutHom automorphism).hom.app X x =
      SMul.smul targetElement x
  calc
    (morphism.fiberAutHom automorphism).hom.app X x =
        (morphism.fiberAutHom automorphism) •
          morphism.fiberIso.hom.app X point := by
            rw [cancellation]
            rfl
    _ = morphism.fiberIso.hom.app X
          (automorphism • point) :=
      pointedEquivariance
    _ = morphism.fiberIso.hom.app X (h • point) := by
      rw [sourceActs]
    _ = SMul.smul targetElement
          (morphism.fiberIso.hom.app X point) :=
      inclusionEquivariance
    _ = SMul.smul targetElement x := by rw [cancellation]

/-- Equality in `ProfiniteGrp` between the group map derived from the selected
pointed pullback and the recovered open-subgroup inclusion. -/
theorem connectedPointedHom_fundamentalGroupHom_eq
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    factorization.connectedPointedHom.fundamentalGroupHom =
      factorization.connectedObjectProfiniteInclusion := by
  ext h
  exact factorization.connectedPointedHom_fundamentalGroupHom h

/-- The inclusion of the recovered stabilizer is an open embedding. -/
theorem connectedObjectProfiniteInclusion_isOpenEmbedding
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    Topology.IsOpenEmbedding
      factorization.connectedObjectProfiniteInclusion := by
  let H := factorization.connectedObjectOpenStabilizer
  letI : IsTopologicalGroup H :=
    Topology.IsInducing.subtypeVal.topologicalGroup H.toSubgroup.subtype
  letI : CompactSpace H :=
    isCompact_iff_compactSpace.mp H.isClosed.isCompact
  exact H.isOpen.isOpenEmbedding_subtypeVal

/-- The connected finite-etale pullback, equipped with the basepoints selected
by its connected-slice classification.  Its induced map on fundamental groups
is the recovered open-subgroup inclusion. -/
noncomputable def connectedFiniteEtaleHom
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    SourceConnectedFiniteEtaleHom
      factorization.connectedSourceEtaleFundamentalGroup
      (continuousActionEtaleFundamentalGroup G) where
  toPointedHom := factorization.connectedPointedHom
  fundamentalGroupIsOpenEmbedding := by
    rw [factorization.connectedPointedHom_fundamentalGroupHom_eq]
    exact factorization.connectedObjectProfiniteInclusion_isOpenEmbedding

/-- The packaged connected finite-etale morphism still exposes the literal
recovered open-subgroup inclusion as its fundamental-group map. -/
theorem connectedFiniteEtaleHom_fundamentalGroupHom_eq
    (factorization : SourceFiniteEtaleFunctorFactorization pullback) :
    factorization.connectedFiniteEtaleHom.toPointedHom.fundamentalGroupHom =
      factorization.connectedObjectProfiniteInclusion :=
  factorization.connectedPointedHom_fundamentalGroupHom_eq

end SourceFiniteEtaleFunctorFactorization

end Iut
