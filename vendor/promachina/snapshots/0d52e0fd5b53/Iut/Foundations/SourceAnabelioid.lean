/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.GaloisImage
import Iut.Foundations.Orbicurve

/-!
# Source-faithful pointed morphisms of connected anabelioids

In *The Geometry of Anabelioids*, Definitions 1.1.1 and 1.1.2, a connected
anabelioid is a Galois category and a morphism is an exact functor in the
opposite direction.  After basepoints are chosen, such a morphism induces a
continuous homomorphism of profinite fundamental groups.

`EtaleFundamentalGroup` already packages a Galois category, a fiber functor, a
profinite group acting on every fiber, and Mathlib's
`PreGaloisCategory.IsFundamentalGroup` certificate.  The structure below adds
the missing source datum for a pointed morphism: an exact pullback functor and
an identification of the pulled-back basepoint with the chosen target
basepoint.  Its homomorphism on fundamental groups is derived, not supplied.
-/

namespace Iut

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

/-! ## Continuity of the two functor-category operations -/

/-- Precomposition of a fiber functor induces a continuous homomorphism on its
automorphism group.  The target topology is initial with respect to evaluation,
and evaluation after precomposition at `Y` is evaluation at `pullback.obj Y`. -/
theorem continuous_mapAut_whiskeringLeft
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (pullback : D ⥤ C) (fiber : C ⥤ FintypeCat.{u}) :
    Continuous
      (((Functor.whiskeringLeft D C FintypeCat.{u}).obj pullback).mapAut fiber) := by
  rw [Topology.IsInducing.continuous_iff
    (autEmbedding_isClosedEmbedding
      (((Functor.whiskeringLeft D C FintypeCat.{u}).obj pullback).obj fiber)).isInducing]
  rw [continuous_pi_iff]
  intro Y
  change Continuous (fun automorphism : Aut fiber =>
    autEmbedding fiber automorphism (pullback.obj Y))
  exact (continuous_apply (pullback.obj Y)).comp continuous_induced_dom

/-- Conjugating natural automorphisms through an isomorphism of fiber functors
is continuous for their canonical profinite topologies. -/
theorem continuous_conjAut
    {C : Type (u + 1)} [Category.{u} C]
    {first second : C ⥤ FintypeCat.{u}}
    (identification : first ≅ second) :
    Continuous identification.conjAut := by
  rw [Topology.IsInducing.continuous_iff
    (autEmbedding_isClosedEmbedding second).isInducing]
  rw [continuous_pi_iff]
  intro X
  change Continuous (fun automorphism : Aut first =>
    (identification.app X).conjAut
      (autEmbedding first automorphism X))
  fun_prop

/-! ## Pointed morphisms and their fundamental-group maps -/

/--
A pointed morphism of connected anabelioids.

The functor is contravariant, as in *The Geometry of Anabelioids*,
Definition 1.1.2(i).  Exactness is represented by preservation of all finite
limits and finite colimits.  `fiberIso` is the chosen compatibility of
basepoints needed to replace the source's outer homomorphism by an actual
homomorphism.
-/
structure SourcePointedAnabelioidHom
    (source target : EtaleFundamentalGroup.{u}) where
  pullback :
    letI := target.coverCategory
    letI := source.coverCategory
    target.Cover ⥤ source.Cover
  preservesFiniteLimits :
    letI := target.coverCategory
    letI := source.coverCategory
    PreservesFiniteLimits pullback
  preservesFiniteColimits :
    letI := target.coverCategory
    letI := source.coverCategory
    PreservesFiniteColimits pullback
  fiberIso :
    letI := target.coverCategory
    letI := source.coverCategory
    pullback ⋙ source.fiber ≅ target.fiber

namespace SourcePointedAnabelioidHom

variable {source middle target : EtaleFundamentalGroup.{u}}

/-- Pullback along a pointed anabelioid morphism is faithful.  This follows
from its compatibility with the two faithful fiber functors. -/
noncomputable instance pullbackFaithful
    (morphism : SourcePointedAnabelioidHom source target) :
    letI := target.coverCategory
    letI := source.coverCategory
    morphism.pullback.Faithful := by
  letI := target.coverCategory
  letI := source.coverCategory
  letI := target.galoisCategory
  letI := source.galoisCategory
  letI := target.fiberFunctor
  letI := source.fiberFunctor
  exact Functor.Faithful.of_comp_iso morphism.fiberIso

/-- Pullback along a pointed anabelioid morphism reflects isomorphisms.  An
isomorphism after pullback is detected by the target fiber functor via the
chosen fiber comparison. -/
noncomputable instance pullbackReflectsIsomorphisms
    (morphism : SourcePointedAnabelioidHom source target) :
    letI := target.coverCategory
    letI := source.coverCategory
    morphism.pullback.ReflectsIsomorphisms := by
  letI := target.coverCategory
  letI := source.coverCategory
  letI := target.galoisCategory
  letI := source.galoisCategory
  letI := target.fiberFunctor
  letI := source.fiberFunctor
  letI : (morphism.pullback ⋙ source.fiber).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_iso morphism.fiberIso.symm
  exact reflectsIsomorphisms_of_comp morphism.pullback source.fiber

/-- Pullback along a pointed exact morphism preserves epimorphisms.  The
chosen fiber comparison carries an epi to a surjection on the source fiber,
and fiber functors reflect epis through their full finite-action lift. -/
noncomputable instance pullbackPreservesEpimorphisms
    (morphism : SourcePointedAnabelioidHom source target) :
    letI := target.coverCategory
    letI := source.coverCategory
    morphism.pullback.PreservesEpimorphisms := by
  letI := target.coverCategory
  letI := source.coverCategory
  letI := target.galoisCategory
  letI := source.galoisCategory
  letI := target.fiberFunctor
  letI := source.fiberFunctor
  letI : (morphism.pullback ⋙ source.fiber).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms.of_iso morphism.fiberIso.symm
  exact
    { preserves := fun pullbackMorphism _ => by
        apply source.fiber.epi_of_epi_map
        change Epi ((morphism.pullback ⋙ source.fiber).map pullbackMorphism)
        infer_instance }

/-- Identity pointed morphism. -/
def identity (data : EtaleFundamentalGroup.{u}) :
    SourcePointedAnabelioidHom data data := by
  letI := data.coverCategory
  exact
    { pullback := 𝟭 data.Cover
      preservesFiniteLimits := inferInstance
      preservesFiniteColimits := inferInstance
      fiberIso := Functor.leftUnitor data.fiber }

/-- Composition of pointed morphisms.  Pullback functors compose in the
contravariant order, and the fiber identification is the corresponding
associator followed by the two chosen basepoint identifications. -/
def comp
    (first : SourcePointedAnabelioidHom source middle)
    (second : SourcePointedAnabelioidHom middle target) :
    SourcePointedAnabelioidHom source target := by
  letI := source.coverCategory
  letI := middle.coverCategory
  letI := target.coverCategory
  letI : PreservesFiniteLimits first.pullback :=
    first.preservesFiniteLimits
  letI : PreservesFiniteColimits first.pullback :=
    first.preservesFiniteColimits
  letI : PreservesFiniteLimits second.pullback :=
    second.preservesFiniteLimits
  letI : PreservesFiniteColimits second.pullback :=
    second.preservesFiniteColimits
  exact
    { pullback := second.pullback ⋙ first.pullback
      preservesFiniteLimits := inferInstance
      preservesFiniteColimits := inferInstance
      fiberIso :=
        Functor.associator
            second.pullback first.pullback source.fiber ≪≫
          Functor.isoWhiskerLeft second.pullback first.fiberIso ≪≫
          second.fiberIso }

/-- The homomorphism between automorphism groups of the chosen fiber functors:
precompose an automorphism and then transport it through the basepoint
identification. -/
def fiberAutHom (morphism : SourcePointedAnabelioidHom source target) :
    letI := target.coverCategory
    letI := source.coverCategory
    Aut source.fiber →* Aut target.fiber := by
  letI := target.coverCategory
  letI := source.coverCategory
  let precomposition :
      Aut source.fiber →* Aut (morphism.pullback ⋙ source.fiber) :=
    ((Functor.whiskeringLeft
      target.Cover source.Cover FintypeCat).obj
        morphism.pullback).mapAut source.fiber
  exact morphism.fiberIso.conjAut.toMonoidHom.comp precomposition

/-- The derived map on fiber-functor automorphism groups is continuous. -/
theorem continuous_fiberAutHom
    (morphism : SourcePointedAnabelioidHom source target) :
    letI := target.coverCategory
    letI := source.coverCategory
    Continuous morphism.fiberAutHom := by
  letI := target.coverCategory
  letI := source.coverCategory
  exact (continuous_conjAut morphism.fiberIso).comp
    (continuous_mapAut_whiskeringLeft morphism.pullback source.fiber)

/-- A certified fundamental group is canonically homeomorphic to the
automorphism group of its fiber functor. -/
noncomputable def certifiedFundamentalGroupEquiv
    (data : EtaleFundamentalGroup.{u}) :
    data.group ≃ₜ* by
      letI := data.coverCategory
      letI := data.galoisCategory
      letI := data.fiberFunctor
      exact Aut data.fiber := by
  letI := data.coverCategory
  letI := data.galoisCategory
  letI := data.fiberFunctor
  letI (X : data.Cover) : MulAction data.group (data.fiber.obj X) :=
    data.action X
  letI : PreGaloisCategory.IsFundamentalGroup data.fiber data.group :=
    data.isFundamentalGroup
  refine ContinuousMulEquiv.mk'
    (PreGaloisCategory.toAutHomeo data.fiber data.group) ?_
  intro first second
  exact map_mul
    (PreGaloisCategory.toAut data.fiber data.group) first second

/--
The continuous homomorphism on the chosen profinite fundamental groups.

It is the composite
`pi(source) -> Aut(fiber_source) -> Aut(fiber_target) -> pi(target)`.
Every arrow is canonical from the two
`IsFundamentalGroup` certificates and the pointed exact functor.
-/
noncomputable def fundamentalGroupContinuousHom
    (morphism : SourcePointedAnabelioidHom source target) :
    source.group →ₜ* target.group := by
  letI := target.coverCategory
  letI := source.coverCategory
  let sourceComparison := certifiedFundamentalGroupEquiv source
  let targetComparison := certifiedFundamentalGroupEquiv target
  let middle : Aut source.fiber →ₜ* Aut target.fiber :=
    { toMonoidHom := morphism.fiberAutHom
      continuous_toFun := morphism.continuous_fiberAutHom }
  exact
    (ContinuousMonoidHom.toContinuousMonoidHom targetComparison.symm).comp
      (middle.comp
        (ContinuousMonoidHom.toContinuousMonoidHom sourceComparison))

/-- The actual morphism in the category of profinite groups induced by a
pointed morphism of connected anabelioids. -/
noncomputable def fundamentalGroupHom
    (morphism : SourcePointedAnabelioidHom source target) :
    source.group ⟶ target.group :=
  ProfiniteGrp.ofHom morphism.fundamentalGroupContinuousHom

/-- The derived map is characterized on every fiber by the basepoint
identification. -/
theorem fiberIso_equivariant
    (morphism : SourcePointedAnabelioidHom source target) :
    letI := target.coverCategory
    letI := source.coverCategory
    ∀ (automorphism : Aut source.fiber)
      (X : target.Cover)
      (point : source.fiber.obj (morphism.pullback.obj X)),
      (morphism.fiberAutHom automorphism) •
          (morphism.fiberIso.hom.app X point) =
        morphism.fiberIso.hom.app X (automorphism • point) := by
  letI := target.coverCategory
  letI := source.coverCategory
  intro automorphism X point
  change
    ((morphism.fiberIso.conjAut
      (((Functor.whiskeringLeft
        target.Cover source.Cover FintypeCat).obj
          morphism.pullback).mapAut source.fiber automorphism)).hom.app X)
        (morphism.fiberIso.hom.app X point) =
      morphism.fiberIso.hom.app X (automorphism.hom.app _ point)
  simp only [Iso.conjAut_hom, Iso.conj_apply, NatTrans.comp_app,
    FintypeCat.comp_apply]
  have cancellation :
      morphism.fiberIso.inv.app X
          (morphism.fiberIso.hom.app X point) = point :=
    FintypeCat.hom_inv_id_apply (morphism.fiberIso.app X) point
  rw [cancellation]
  rfl

/-- Identity induces the identity automorphism on the chosen fiber functor. -/
theorem fiberAutHom_identity
    (data : EtaleFundamentalGroup.{u}) :
    letI := data.coverCategory
    ∀ automorphism : Aut data.fiber,
      (identity data).fiberAutHom automorphism = automorphism := by
  letI := data.coverCategory
  intro automorphism
  ext X point
  rfl

/-- The automorphism-group map of a composite pointed morphism is the
composite of the two automorphism-group maps. -/
theorem fiberAutHom_comp
    (first : SourcePointedAnabelioidHom source middle)
    (second : SourcePointedAnabelioidHom middle target) :
    letI := source.coverCategory
    letI := middle.coverCategory
    letI := target.coverCategory
    ∀ automorphism : Aut source.fiber,
      (first.comp second).fiberAutHom automorphism =
        second.fiberAutHom (first.fiberAutHom automorphism) := by
  letI := source.coverCategory
  letI := middle.coverCategory
  letI := target.coverCategory
  intro automorphism
  ext X point
  change
    second.fiberIso.hom.app X
        (first.fiberIso.hom.app (second.pullback.obj X)
          (automorphism.hom.app
            (first.pullback.obj (second.pullback.obj X))
            (first.fiberIso.inv.app (second.pullback.obj X)
              (second.fiberIso.inv.app X point)))) =
      second.fiberIso.hom.app X
        (first.fiberIso.hom.app (second.pullback.obj X)
          (automorphism.hom.app
            (first.pullback.obj (second.pullback.obj X))
            (first.fiberIso.inv.app (second.pullback.obj X)
              (second.fiberIso.inv.app X point))))
  rfl

/-- Under the canonical `IsFundamentalGroup` comparisons, the profinite-group
map is exactly the map on automorphisms of the chosen fiber functors. -/
theorem certifiedFundamentalGroupEquiv_fundamentalGroupHom
    (morphism : SourcePointedAnabelioidHom source target) :
    letI := source.coverCategory
    letI := target.coverCategory
    ∀ element : source.group,
      certifiedFundamentalGroupEquiv target
          (morphism.fundamentalGroupHom element) =
        morphism.fiberAutHom
          (certifiedFundamentalGroupEquiv source element) := by
  letI := source.coverCategory
  letI := target.coverCategory
  intro element
  change
    certifiedFundamentalGroupEquiv target
        (morphism.fundamentalGroupContinuousHom element) =
      morphism.fiberAutHom
        (certifiedFundamentalGroupEquiv source element)
  simp [fundamentalGroupContinuousHom]
  rfl

/-- Functoriality of the induced maps on the certified profinite fundamental
groups. -/
theorem fundamentalGroupHom_comp
    (first : SourcePointedAnabelioidHom source middle)
    (second : SourcePointedAnabelioidHom middle target)
    (element : source.group) :
    (first.comp second).fundamentalGroupHom element =
      second.fundamentalGroupHom
        (first.fundamentalGroupHom element) := by
  letI := source.coverCategory
  letI := middle.coverCategory
  letI := target.coverCategory
  apply (certifiedFundamentalGroupEquiv target).injective
  rw [certifiedFundamentalGroupEquiv_fundamentalGroupHom
    (first.comp second) element]
  rw [certifiedFundamentalGroupEquiv_fundamentalGroupHom
    second (first.fundamentalGroupHom element)]
  rw [certifiedFundamentalGroupEquiv_fundamentalGroupHom
    first element]
  exact first.fiberAutHom_comp second _

/-- The identity pointed morphism induces the identity on the certified
profinite fundamental group. -/
theorem fundamentalGroupHom_identity
    (data : EtaleFundamentalGroup.{u}) (element : data.group) :
    (identity data).fundamentalGroupHom element = element := by
  letI := data.coverCategory
  apply (certifiedFundamentalGroupEquiv data).injective
  rw [certifiedFundamentalGroupEquiv_fundamentalGroupHom]
  rw [fiberAutHom_identity]

/-! ## Two-isomorphisms and the inner ambiguity of unpointed morphisms -/

/--
A 2-isomorphism between the exact pullback functors underlying two pointed
anabelioid morphisms.

It is deliberately not required to preserve the chosen `fiberIso`s.  Their
failure to agree is precisely the inner-conjugacy ambiguity of the induced
fundamental-group homomorphisms in *The Geometry of Anabelioids*,
Proposition 1.1.4.
-/
structure TwoIso
    (first second : SourcePointedAnabelioidHom source target) where
  pullbackIso :
    letI := source.coverCategory
    letI := target.coverCategory
    first.pullback ≅ second.pullback

namespace TwoIso

variable
    {first second : SourcePointedAnabelioidHom source target}
    (comparison : TwoIso first second)

/-- The discrepancy between the two chosen basepoint identifications. -/
def fiberDiscrepancy :
    letI := source.coverCategory
    letI := target.coverCategory
    Aut target.fiber := by
  letI := source.coverCategory
  letI := target.coverCategory
  exact first.fiberIso.symm ≪≫
    Functor.isoWhiskerRight comparison.pullbackIso source.fiber ≪≫
      second.fiberIso

/-- Precomposition along naturally isomorphic pullback functors gives
conjugate automorphisms of the pulled-back fiber functors. -/
theorem precomposition_conjugate
    (automorphism : Aut source.fiber) :
    letI := source.coverCategory
    letI := target.coverCategory
    ((Functor.whiskeringLeft
        target.Cover source.Cover FintypeCat).obj
          second.pullback).mapAut source.fiber automorphism =
      (Functor.isoWhiskerRight
        comparison.pullbackIso source.fiber).conjAut
          (((Functor.whiskeringLeft
            target.Cover source.Cover FintypeCat).obj
              first.pullback).mapAut source.fiber automorphism) := by
  letI := source.coverCategory
  letI := target.coverCategory
  apply Aut.ext
  ext X point
  change
    automorphism.hom.app (second.pullback.obj X) point =
      source.fiber.map (comparison.pullbackIso.hom.app X)
        (automorphism.hom.app (first.pullback.obj X)
          (source.fiber.map (comparison.pullbackIso.inv.app X) point))
  rw [← automorphism.hom.naturality_apply]
  have mapCancellation :
      source.fiber.map (comparison.pullbackIso.inv.app X) ≫
          source.fiber.map (comparison.pullbackIso.hom.app X) =
        𝟙 _ := by
    rw [← source.fiber.map_comp]
    rw [comparison.pullbackIso.inv_hom_id_app]
    simp
  have pointCancellation :=
    ConcreteCategory.congr_hom mapCancellation point
  simpa only [FintypeCat.comp_apply, FintypeCat.id_apply] using
    congrArg
      (fun value =>
        automorphism.hom.app (second.pullback.obj X) value)
      pointCancellation.symm

/-- The maps on fiber-functor automorphism groups differ by conjugation by
the basepoint discrepancy. -/
theorem fiberAutHom_eq_conjugate
    (automorphism : Aut source.fiber) :
    letI := source.coverCategory
    letI := target.coverCategory
    second.fiberAutHom automorphism =
      comparison.fiberDiscrepancy.conjAut
        (first.fiberAutHom automorphism) := by
  letI := source.coverCategory
  letI := target.coverCategory
  let pulledIdentification :=
    Functor.isoWhiskerRight comparison.pullbackIso source.fiber
  let firstPrecomposition :=
    ((Functor.whiskeringLeft
      target.Cover source.Cover FintypeCat).obj
        first.pullback).mapAut source.fiber automorphism
  let secondPrecomposition :=
    ((Functor.whiskeringLeft
      target.Cover source.Cover FintypeCat).obj
        second.pullback).mapAut source.fiber automorphism
  have precompositionEquality :
      secondPrecomposition =
        pulledIdentification.conjAut firstPrecomposition :=
    comparison.precomposition_conjugate automorphism
  rw [show second.fiberAutHom automorphism =
      second.fiberIso.conjAut secondPrecomposition by rfl]
  rw [precompositionEquality]
  rw [← Iso.trans_conjAut]
  rw [show first.fiberAutHom automorphism =
      first.fiberIso.conjAut firstPrecomposition by rfl]
  rw [← Iso.trans_conjAut]
  congr 1
  simp [fiberDiscrepancy, pulledIdentification]

/-- For an automorphism `transport`, categorical conjugation is ordinary
group conjugation `transport * value * transport^-1`. -/
theorem conjAut_eq_mul
    :
    letI := target.coverCategory
    ∀ (transport value : Aut target.fiber),
      transport.conjAut value =
        transport * value * transport⁻¹ := by
  letI := target.coverCategory
  intro transport value
  ext X point
  rfl

/-- The group element corresponding to the basepoint discrepancy. -/
noncomputable def fundamentalGroupTransport : target.group := by
  letI := source.coverCategory
  letI := target.coverCategory
  exact (certifiedFundamentalGroupEquiv target).symm
    comparison.fiberDiscrepancy

/-- Applying the canonical comparison to the derived transport recovers the
fiber-functor discrepancy. -/
theorem certifiedFundamentalGroupEquiv_transport :
    certifiedFundamentalGroupEquiv target
        comparison.fundamentalGroupTransport =
      comparison.fiberDiscrepancy := by
  letI := source.coverCategory
  letI := target.coverCategory
  exact (certifiedFundamentalGroupEquiv target).apply_symm_apply _

/-- The source's outer-homomorphism ambiguity, now derived from an actual
2-isomorphism: the two maps on certified profinite fundamental groups differ
by conjugation by the group element attached to the basepoint discrepancy. -/
theorem fundamentalGroupHom_eq_conjugate
    (element : source.group) :
    second.fundamentalGroupHom element =
      comparison.fundamentalGroupTransport *
          first.fundamentalGroupHom element *
        comparison.fundamentalGroupTransport⁻¹ := by
  letI := source.coverCategory
  letI := target.coverCategory
  apply (certifiedFundamentalGroupEquiv target).injective
  rw [second.certifiedFundamentalGroupEquiv_fundamentalGroupHom]
  rw [map_mul, map_mul, map_inv]
  rw [comparison.certifiedFundamentalGroupEquiv_transport]
  rw [first.certifiedFundamentalGroupEquiv_fundamentalGroupHom]
  rw [comparison.fiberAutHom_eq_conjugate]
  exact conjAut_eq_mul (target := target) _ _

end TwoIso

/-- The source paper's `pi_1`-monomorphism condition, stated for the actual
derived fundamental-group homomorphism. -/
def IsPiOneMonomorphism
    (morphism : SourcePointedAnabelioidHom source target) : Prop :=
  Function.Injective morphism.fundamentalGroupHom

/-- The image of the derived fundamental-group map. -/
noncomputable def fundamentalGroupImage
    (morphism : SourcePointedAnabelioidHom source target) :
    Subgroup target.group :=
  morphism.fundamentalGroupHom.hom.range

/-- The fundamental-group image of any pointed anabelioid morphism is closed:
it is the continuous image of a compact profinite group in a Hausdorff
profinite group. -/
theorem fundamentalGroupImage_isClosed
    (morphism : SourcePointedAnabelioidHom source target) :
    IsClosed (morphism.fundamentalGroupImage : Set target.group) := by
  change IsClosed (Set.range morphism.fundamentalGroupHom)
  simpa only [Set.image_univ] using
    (isCompact_univ.image
      morphism.fundamentalGroupContinuousHom.continuous).isClosed

/-- The image, with its induced topology, as a closed subgroup of the target
fundamental group. -/
noncomputable def fundamentalGroupClosedImage
    (morphism : SourcePointedAnabelioidHom source target) :
    ClosedSubgroup target.group where
  toSubgroup := morphism.fundamentalGroupImage
  isClosed' := morphism.fundamentalGroupImage_isClosed

/-- The fundamental-group map with codomain restricted to its closed image. -/
noncomputable def fundamentalGroupRangeHom
    (morphism : SourcePointedAnabelioidHom source target) :
    source.group →* morphism.fundamentalGroupClosedImage :=
  morphism.fundamentalGroupHom.hom.toMonoidHom.rangeRestrict

/-- A `pi_1`-monomorphism identifies its source group algebraically with its
actual image subgroup. -/
noncomputable def fundamentalGroupImageMulEquiv
    (morphism : SourcePointedAnabelioidHom source target)
    (injective : morphism.IsPiOneMonomorphism) :
    source.group ≃* morphism.fundamentalGroupClosedImage := by
  refine MulEquiv.ofBijective morphism.fundamentalGroupRangeHom
    ⟨?_, ?_⟩
  · intro first second equality
    apply injective
    exact congrArg Subtype.val equality
  · intro value
    rcases value.2 with ⟨preimage, equality⟩
    refine ⟨preimage, ?_⟩
    exact Subtype.ext equality

/-- A `pi_1`-monomorphism identifies its certified source fundamental group
homeomorphically with the closed image subgroup, not merely with an abstract
isomorphic group. -/
noncomputable def fundamentalGroupImageContinuousMulEquiv
    (morphism : SourcePointedAnabelioidHom source target)
    (injective : morphism.IsPiOneMonomorphism) :
    source.group ≃ₜ* morphism.fundamentalGroupClosedImage where
  toMulEquiv := morphism.fundamentalGroupImageMulEquiv injective
  continuous_toFun := by
    exact morphism.fundamentalGroupContinuousHom.continuous.subtype_mk _
  continuous_invFun := by
    have continuousForward :
        Continuous (morphism.fundamentalGroupImageMulEquiv injective) :=
      morphism.fundamentalGroupContinuousHom.continuous.subtype_mk _
    exact Continuous.continuous_symm_of_equiv_compact_to_t2
      continuousForward

/-- A pointed `pi_1`-monomorphism yields an actual injective morphism of
profinite groups. -/
noncomputable def toProfiniteEmbedding
    (morphism : SourcePointedAnabelioidHom source target)
    (injective : morphism.IsPiOneMonomorphism) :
    ProfiniteEmbedding source.group target.group where
  hom := morphism.fundamentalGroupHom
  injective := injective

end SourcePointedAnabelioidHom

end Iut
