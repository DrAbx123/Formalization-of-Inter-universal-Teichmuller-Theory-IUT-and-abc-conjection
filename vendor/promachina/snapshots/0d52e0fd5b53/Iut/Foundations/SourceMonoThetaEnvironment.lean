/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceInitialThetaData
import Iut.Foundations.SourceTemperedSemigraph
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.PNat.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Source boundary for mono-theta environments and their inverse limits

This module formalizes the group-theoretic data in *The Etale Theta
Function and its Frobenioid-theoretic Manifestations*, Definition 2.13, and
the inverse-limit clause of IUT II, Definition 2.7(i).

The ambient groups are genuine topological groups.  The theta-section
collection is the conjugacy class of the image of a continuous injective
homomorphism, and an outer subgroup is represented by its full inverse image
in the continuous automorphism group.  This avoids replacing `Out(Pi)` by an
unrelated finite action.

No constructor from initial theta data is provided here: constructing the
tempered fundamental groups, Kummer extensions, and transition reductions is
the remaining source obligation.  The profinite standard-type realization does,
however, construct its theta-root cover and theta-center subquotient below from
the exact quotient diagrams of *Etale Theta*, Section 2.
-/

open CategoryTheory

namespace Iut

universe u

/-- Topological groups and continuous homomorphisms, without a compactness assumption. -/
structure TopologicalGroupCat where
  toFundamentalGroup : AbstractFundamentalGroup.{u}

namespace TopologicalGroupCat

instance : CoeSort TopologicalGroupCat.{u} (Type u) :=
  ⟨fun G => G.toFundamentalGroup.carrier⟩

instance (G : TopologicalGroupCat) : Group G :=
  G.toFundamentalGroup.group

instance (G : TopologicalGroupCat) : TopologicalSpace G :=
  G.toFundamentalGroup.topology

instance (G : TopologicalGroupCat) : IsTopologicalGroup G :=
  G.toFundamentalGroup.isTopologicalGroup

instance : Category TopologicalGroupCat where
  Hom G H := G →ₜ* H
  id G := _root_.ContinuousMonoidHom.id G
  comp f g := g.comp f
  assoc _ _ _ := by
    apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  id_comp _ := by
    apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  comp_id _ := by
    apply _root_.ContinuousMonoidHom.ext
    intro
    rfl

/-- A profinite group regarded as a topological group object. -/
def ofProfinite (G : ProfiniteGrp.{u}) : TopologicalGroupCat where
  toFundamentalGroup :=
    { carrier := G
      group := inferInstance
      topology := inferInstance
      isTopologicalGroup := inferInstance
      topologyKind := .profinite }

noncomputable instance ofProfiniteCompactSpace (G : ProfiniteGrp.{u}) :
    CompactSpace (ofProfinite G) := by
  change CompactSpace G
  infer_instance

noncomputable instance ofProfiniteT2Space (G : ProfiniteGrp.{u}) :
    T2Space (ofProfinite G) := by
  change T2Space G
  infer_instance

noncomputable instance ofProfiniteTotallyDisconnectedSpace
    (G : ProfiniteGrp.{u}) :
    TotallyDisconnectedSpace (ofProfinite G) := by
  change TotallyDisconnectedSpace G
  infer_instance

/-- A subgroup with its induced topological-group structure. -/
def ofSubgroup
    (G : TopologicalGroupCat.{u})
    (H : Subgroup G) :
    TopologicalGroupCat.{u} where
  toFundamentalGroup :=
    { carrier := H
      group := inferInstance
      topology := inferInstance
      isTopologicalGroup := inferInstance
      topologyKind :=
        G.toFundamentalGroup.topologyKind }

/-- The continuous inclusion of a subgroup into its ambient topological group. -/
def subgroupInclusion
    (G : TopologicalGroupCat.{u})
    (H : Subgroup G) :
    ofSubgroup G H ⟶ G where
  toMonoidHom := H.subtype
  continuous_toFun := continuous_subtype_val

/-- The identity morphism with its continuous-group-homomorphism structure exposed. -/
def identity (G : TopologicalGroupCat.{u}) : G ⟶ G where
  toMonoidHom := MonoidHom.id G
  continuous_toFun := continuous_id

@[simp]
theorem identity_apply (G : TopologicalGroupCat.{u}) (g : G) :
    (identity G).toMonoidHom g = g :=
  rfl

end TopologicalGroupCat

/--
A topological group subquotient `U / N`.

Both groups are derived from the ambient group: `U` is an actual subgroup and
`N` is an actual normal subgroup of `U`.  In particular, the carrier is not an
unrelated type merely equipped with a comparison map.
-/
structure SourceTopologicalSubquotient
    (G : TopologicalGroupCat.{u}) where
  numerator : Subgroup G
  denominator : Subgroup numerator
  denominator_normal :
    denominator.Normal

namespace SourceTopologicalSubquotient

variable {G : TopologicalGroupCat.{u}}

instance (Q : SourceTopologicalSubquotient G) :
    Q.denominator.Normal :=
  Q.denominator_normal

/-- The actual quotient carrier `U / N`. -/
abbrev Carrier
    (Q : SourceTopologicalSubquotient G) : Type u :=
  Q.numerator ⧸ Q.denominator

/-- A source subquotient regarded as a topological group object. -/
def toTopologicalGroupCat
    (Q : SourceTopologicalSubquotient G) :
    TopologicalGroupCat.{u} where
  toFundamentalGroup :=
    { carrier := Q.Carrier
      group := inferInstance
      topology := inferInstance
      isTopologicalGroup := inferInstance
      topologyKind := .abstract }

/-- The continuous quotient projection `U -> U / N`. -/
def projection
    (Q : SourceTopologicalSubquotient G) :
    Q.numerator →ₜ* Q.Carrier where
  toMonoidHom :=
    QuotientGroup.mk' Q.denominator
  continuous_toFun :=
    QuotientGroup.continuous_mk

/-- The homomorphism from a pulled-back numerator to the original numerator. -/
def comapNumeratorHom
    {H : TopologicalGroupCat.{u}}
    (Q : SourceTopologicalSubquotient G)
    (f : H ⟶ G) :
    Subgroup.comap f.toMonoidHom Q.numerator →*
      Q.numerator where
  toFun h := ⟨f.toMonoidHom h.1, h.2⟩
  map_one' := by
    apply SetCoe.ext
    exact map_one f.toMonoidHom
  map_mul' first second := by
    apply SetCoe.ext
    exact map_mul f.toMonoidHom first.1 second.1

/--
Pull a topological subquotient `U/N` back along a continuous group
homomorphism, obtaining `f⁻¹(U)/f⁻¹(N)`.
-/
def comap
    {H : TopologicalGroupCat.{u}}
    (Q : SourceTopologicalSubquotient G)
    (f : H ⟶ G) :
    SourceTopologicalSubquotient H where
  numerator :=
    Subgroup.comap f.toMonoidHom Q.numerator
  denominator :=
    Subgroup.comap (Q.comapNumeratorHom f)
      Q.denominator
  denominator_normal :=
    Q.denominator_normal.comap
      (Q.comapNumeratorHom f)

/-- The canonical map from a pulled-back subquotient to the original
subquotient. Its denominator condition is derived from the pullback. -/
def comapToOriginal
    {H : TopologicalGroupCat.{u}}
    (Q : SourceTopologicalSubquotient G)
    (f : H ⟶ G) :
    (Q.comap f).Carrier →* Q.Carrier :=
  QuotientGroup.map
    (Q.comap f).denominator
    Q.denominator
    (Q.comapNumeratorHom f)
    (by
      intro source hsource
      exact hsource)

@[simp]
theorem comapToOriginal_projection
    {H : TopologicalGroupCat.{u}}
    (Q : SourceTopologicalSubquotient G)
    (f : H ⟶ G)
    (source : (Q.comap f).numerator) :
    Q.comapToOriginal f ((Q.comap f).projection source) =
      Q.projection (Q.comapNumeratorHom f source) :=
  rfl

/-- Pullback makes the induced quotient map injective: its kernel has already
been pulled back into the source denominator. -/
theorem comapToOriginal_injective
    {H : TopologicalGroupCat.{u}}
    (Q : SourceTopologicalSubquotient G)
    (f : H ⟶ G) :
    Function.Injective (Q.comapToOriginal f) := by
  intro first second heq
  induction first using QuotientGroup.induction_on with
  | _ first =>
      induction second using QuotientGroup.induction_on with
      | _ second =>
          apply QuotientGroup.eq_iff_div_mem.mpr
          change
            Q.comapNumeratorHom f (first / second) ∈
              Q.denominator
          have hdenominator :=
            QuotientGroup.eq_iff_div_mem.mp heq
          change
            Q.comapNumeratorHom f first /
                Q.comapNumeratorHom f second ∈
              Q.denominator at hdenominator
          have hmap :
              Q.comapNumeratorHom f (first / second) =
                Q.comapNumeratorHom f first /
                  Q.comapNumeratorHom f second :=
            (Q.comapNumeratorHom f).map_div first second
          exact hmap.symm ▸ hdenominator

/-- The induced quotient map is continuous. -/
theorem continuous_comapToOriginal
    {H : TopologicalGroupCat.{u}}
    (Q : SourceTopologicalSubquotient G)
    (f : H ⟶ G) :
    Continuous (Q.comapToOriginal f) := by
  apply
    (QuotientGroup.isQuotientMap_mk
      (Q.comap f).denominator).continuous_iff.mpr
  change Continuous
    (Q.comapToOriginal f ∘ QuotientGroup.mk)
  have hNumerator : Continuous (Q.comapNumeratorHom f) := by
    apply Continuous.subtype_mk
    exact f.continuous_toFun.comp continuous_subtype_val
  convert Q.projection.continuous.comp hNumerator using 1

/-- Continuous-hom form of the canonical pullback map. -/
def comapToOriginalContinuousHom
    {H : TopologicalGroupCat.{u}}
    (Q : SourceTopologicalSubquotient G)
    (f : H ⟶ G) :
    (Q.comap f).Carrier →ₜ* Q.Carrier where
  toMonoidHom := Q.comapToOriginal f
  continuous_toFun := Q.continuous_comapToOriginal f

/-- Cuspidal inertia gives surjectivity of the restriction map when the
ambient coefficient quotient is generated by ambient cusp inertia and the
subgraph cusp inertia maps onto it. This is the algebraic argument used in
IUT II, Corollary 2.5(i). -/
theorem comapToOriginal_surjective_of_cuspidalInertia
    {H : TopologicalGroupCat.{u}}
    (Q : SourceTopologicalSubquotient G)
    (f : H ⟶ G)
    {SubgraphInertia AmbientInertia : Type u}
    [Group SubgraphInertia] [Group AmbientInertia]
    (subgraphInertia :
      SubgraphInertia →* (Q.comap f).numerator)
    (ambientInertia : AmbientInertia →* Q.numerator)
    (inertiaRestriction : SubgraphInertia →* AmbientInertia)
    (inertiaRestriction_surjective :
      Function.Surjective inertiaRestriction)
    (ambientInertia_generates :
      Function.Surjective
        (Q.projection.toMonoidHom.comp ambientInertia))
    (inertia_square :
      (Q.comapNumeratorHom f).comp subgraphInertia =
        ambientInertia.comp inertiaRestriction) :
    Function.Surjective (Q.comapToOriginal f) := by
  intro target
  obtain ⟨ambient, hambient⟩ :=
    ambientInertia_generates target
  obtain ⟨subgraph, hsubgraph⟩ :=
    inertiaRestriction_surjective ambient
  refine
    ⟨(Q.comap f).projection (subgraphInertia subgraph), ?_⟩
  rw [Q.comapToOriginal_projection]
  have hsquare := DFunLike.congr_fun inertia_square subgraph
  change
    Q.projection
        (Q.comapNumeratorHom f (subgraphInertia subgraph)) =
      target
  change
    Q.comapNumeratorHom f (subgraphInertia subgraph) =
      ambientInertia (inertiaRestriction subgraph) at hsquare
  rw [hsquare, hsubgraph]
  exact hambient

/-- The source restriction is an algebraic isomorphism under the explicit
cuspidal-inertia hypotheses. -/
noncomputable def comapMulEquivOfCuspidalInertia
    {H : TopologicalGroupCat.{u}}
    (Q : SourceTopologicalSubquotient G)
    (f : H ⟶ G)
    {SubgraphInertia AmbientInertia : Type u}
    [Group SubgraphInertia] [Group AmbientInertia]
    (subgraphInertia :
      SubgraphInertia →* (Q.comap f).numerator)
    (ambientInertia : AmbientInertia →* Q.numerator)
    (inertiaRestriction : SubgraphInertia →* AmbientInertia)
    (inertiaRestriction_surjective :
      Function.Surjective inertiaRestriction)
    (ambientInertia_generates :
      Function.Surjective
        (Q.projection.toMonoidHom.comp ambientInertia))
    (inertia_square :
      (Q.comapNumeratorHom f).comp subgraphInertia =
        ambientInertia.comp inertiaRestriction) :
    (Q.comap f).Carrier ≃* Q.Carrier :=
  MulEquiv.ofBijective
    (Q.comapToOriginal f)
    ⟨Q.comapToOriginal_injective f,
      Q.comapToOriginal_surjective_of_cuspidalInertia f
        subgraphInertia ambientInertia inertiaRestriction
        inertiaRestriction_surjective ambientInertia_generates
        inertia_square⟩

/-- With compact source and Hausdorff target, the Corollary 2.5 restriction is
an isomorphism of topological groups. -/
noncomputable def comapContinuousMulEquivOfCuspidalInertia
    {H : TopologicalGroupCat.{u}}
    (Q : SourceTopologicalSubquotient G)
    (f : H ⟶ G)
    {SubgraphInertia AmbientInertia : Type u}
    [Group SubgraphInertia] [Group AmbientInertia]
    [CompactSpace (Q.comap f).Carrier]
    [T2Space Q.Carrier]
    (subgraphInertia :
      SubgraphInertia →* (Q.comap f).numerator)
    (ambientInertia : AmbientInertia →* Q.numerator)
    (inertiaRestriction : SubgraphInertia →* AmbientInertia)
    (inertiaRestriction_surjective :
      Function.Surjective inertiaRestriction)
    (ambientInertia_generates :
      Function.Surjective
        (Q.projection.toMonoidHom.comp ambientInertia))
    (inertia_square :
      (Q.comapNumeratorHom f).comp subgraphInertia =
        ambientInertia.comp inertiaRestriction) :
    (Q.comap f).Carrier ≃ₜ* Q.Carrier := by
  let equivalence : (Q.comap f).Carrier ≃* Q.Carrier :=
    Q.comapMulEquivOfCuspidalInertia f
      subgraphInertia ambientInertia inertiaRestriction
      inertiaRestriction_surjective ambientInertia_generates
      inertia_square
  refine
    { toMulEquiv := equivalence
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · simpa [equivalence] using Q.continuous_comapToOriginal f
  · exact
      Continuous.continuous_symm_of_equiv_compact_to_t2
        (f := equivalence.toEquiv)
        (by simpa [equivalence] using Q.continuous_comapToOriginal f)

end SourceTopologicalSubquotient

/-- A continuous surjective homomorphism of profinite groups is an open
quotient map.  The proof passes through the literal quotient by its closed
kernel, so it also records the topology used by the first isomorphism theorem. -/
theorem profiniteSurjectiveHom_isOpenQuotientMap
    {A B : ProfiniteGrp.{u}}
    (f : A →* B)
    (continuous_f : Continuous f)
    (surjective_f : Function.Surjective f) :
    IsOpenQuotientMap f := by
  have kernel_isClosed :
      IsClosed ((f.ker : Subgroup A) : Set A) := by
    change IsClosed {source : A | f source = 1}
    exact isClosed_singleton.preimage continuous_f
  letI : IsClosed ((f.ker : Subgroup A) : Set A) := kernel_isClosed
  let equivalence : A ⧸ f.ker ≃* B :=
    QuotientGroup.quotientKerEquivOfSurjective f surjective_f
  have continuous_equivalence : Continuous equivalence := by
    apply (QuotientGroup.isQuotientMap_mk f.ker).continuous_iff.mpr
    change Continuous (equivalence ∘ QuotientGroup.mk)
    convert continuous_f using 1
  let continuousEquivalence : A ⧸ f.ker ≃ₜ* B :=
    { toMulEquiv := equivalence
      continuous_toFun := continuous_equivalence
      continuous_invFun :=
        Continuous.continuous_symm_of_equiv_compact_to_t2
          continuous_equivalence }
  have quotient_then_equivalence :
      IsOpenQuotientMap
        (continuousEquivalence ∘
          (QuotientGroup.mk : A → A ⧸ f.ker)) :=
    continuousEquivalence.toHomeomorph.isOpenQuotientMap.comp
      QuotientGroup.isOpenQuotientMap_mk
  convert quotient_then_equivalence using 1

/-- A continuous algebraically exact sequence of profinite groups is a short
exact sequence in topological groups. -/
theorem profiniteExactSequence_isSES
    {A B C : ProfiniteGrp.{u}}
    (inclusion : A →* B)
    (projection : B →* C)
    (inclusion_continuous : Continuous inclusion)
    (projection_continuous : Continuous projection)
    (inclusion_injective : Function.Injective inclusion)
    (projection_surjective : Function.Surjective projection)
    (exact : inclusion.range = projection.ker) :
    TopologicalGroup.IsSES inclusion projection := by
  refine
    { isClosedEmbedding := ?_
      isOpenQuotientMap :=
        profiniteSurjectiveHom_isOpenQuotientMap
          projection projection_continuous projection_surjective
      mulExact := ?_ }
  · apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      inclusion_continuous inclusion_injective
    intro subset hsubset
    exact (hsubset.isCompact.image inclusion_continuous).isClosed
  · intro middle
    change middle ∈ projection.ker ↔ middle ∈ inclusion.range
    rw [exact]

/-!
## Profinite source subquotients

The generic structure above remains useful for noncompact tempered groups.
Continuous cohomology in the canonical Etale Theta coefficient path needs a
strictly stronger boundary: both subgroups are closed, and the literal quotient
is continuously equivalent to an actual profinite group.  This structure
records exactly those facts while retaining the canonical quotient topology,
including when the ambient topological group is not itself profinite.
-/

/-- A literal closed subquotient `U / N` of a topological group, certified by
a homeomorphic profinite model.  In particular, a nonclosed normal subgroup
cannot be used to construct this source object. -/
structure SourceProfiniteSubquotient
    (G : TopologicalGroupCat.{u}) where
  numerator : Subgroup G
  numerator_isClosed : IsClosed ((numerator : Subgroup G) : Set G)
  denominator : Subgroup numerator
  denominator_normal : denominator.Normal
  denominator_isClosed :
    IsClosed ((denominator : Subgroup numerator) : Set numerator)
  profiniteModel : ProfiniteGrp.{u}
  carrierEquiv :
    (numerator ⧸ denominator) ≃ₜ* profiniteModel

namespace SourceProfiniteSubquotient

variable {G : TopologicalGroupCat.{u}}

instance (Q : SourceProfiniteSubquotient G) :
    Q.denominator.Normal :=
  Q.denominator_normal

/-- The actual quotient carrier with Mathlib's quotient topology. -/
abbrev Carrier (Q : SourceProfiniteSubquotient G) : Type u :=
  Q.numerator ⧸ Q.denominator

/-- Forget only the profinite certification, retaining the same literal
topological subquotient. -/
def toTopologicalSubquotient
    (Q : SourceProfiniteSubquotient G) :
    SourceTopologicalSubquotient G where
  numerator := Q.numerator
  denominator := Q.denominator
  denominator_normal := Q.denominator_normal

/-- The continuous quotient projection `U -> U / N`. -/
def projection (Q : SourceProfiniteSubquotient G) :
    Q.numerator →ₜ* Q.Carrier :=
  Q.toTopologicalSubquotient.projection

/-- The literal quotient carrier, now packaged as a profinite group by its
certified homeomorphism to the profinite model. -/
noncomputable def toProfiniteGrp
    (Q : SourceProfiniteSubquotient G) : ProfiniteGrp.{u} :=
  ProfiniteGrp.ofContinuousMulEquiv Q.carrierEquiv.symm

/-- The quotient projection and inclusion form a short exact sequence of
topological groups. -/
theorem isSES (Q : SourceProfiniteSubquotient G) :
    TopologicalGroup.IsSES
      Q.denominator.subtype
      (QuotientGroup.mk' Q.denominator) :=
  TopologicalGroup.IsSES.ofClosedSubgroup
    Q.denominator Q.denominator_isClosed

/-- Regression surface: every denominator admitted by the canonical
profinite source boundary is closed. -/
theorem canonical_denominator_isClosed
    (Q : SourceProfiniteSubquotient G) :
    IsClosed ((Q.denominator : Subgroup Q.numerator) : Set Q.numerator) :=
  Q.denominator_isClosed

/-- A nonclosed normal subgroup cannot be smuggled into the canonical
profinite coefficient path. -/
theorem nonclosed_denominator_not_canonical
    {G : TopologicalGroupCat.{u}}
    (numerator : Subgroup G)
    (denominator : Subgroup numerator)
    (_normal : denominator.Normal)
    (not_closed :
      ¬ IsClosed ((denominator : Subgroup numerator) : Set numerator)) :
    ¬ ∃ Q : SourceProfiniteSubquotient G,
      Q.numerator = numerator ∧ HEq Q.denominator denominator := by
  rintro ⟨Q, rfl, denominator_eq⟩
  cases denominator_eq
  exact not_closed Q.denominator_isClosed

end SourceProfiniteSubquotient

/-- The exact cuspidal-inertia input used by IUT II, Corollary 2.5(i).

The resulting restriction isomorphism is not a field.  The fields state the
two geometric facts invoked in the paper's proof: the ambient coefficient
quotient is generated by cusp inertia, and the cusp inertia of the connected
subgraph maps onto that ambient inertia. -/
structure SourceIUTIICorollary25CuspidalRestriction
    {Ambient Subgraph : TopologicalGroupCat.{u}}
    (Q : SourceTopologicalSubquotient Ambient)
    (inclusion : Subgraph ⟶ Ambient) where
  SubgraphInertia : Type u
  AmbientInertia : Type u
  subgraphInertiaGroup : Group SubgraphInertia
  ambientInertiaGroup : Group AmbientInertia
  subgraphInertia :
    SubgraphInertia →* (Q.comap inclusion).numerator
  ambientInertia : AmbientInertia →* Q.numerator
  inertiaRestriction : SubgraphInertia →* AmbientInertia
  inertiaRestriction_surjective :
    Function.Surjective inertiaRestriction
  ambientInertia_generates :
    Function.Surjective
      (Q.projection.toMonoidHom.comp ambientInertia)
  inertia_square :
    (Q.comapNumeratorHom inclusion).comp subgraphInertia =
      ambientInertia.comp inertiaRestriction

namespace SourceIUTIICorollary25CuspidalRestriction

variable
  {Ambient Subgraph : TopologicalGroupCat.{u}}
  {Q : SourceTopologicalSubquotient Ambient}
  {inclusion : Subgraph ⟶ Ambient}
  (data : SourceIUTIICorollary25CuspidalRestriction Q inclusion)

attribute [local instance]
  SourceIUTIICorollary25CuspidalRestriction.subgraphInertiaGroup
  SourceIUTIICorollary25CuspidalRestriction.ambientInertiaGroup

/-- The inclusion of the subgraph induces an injective map on the pulled-back
coefficient subquotient. -/
theorem restriction_injective :
    Function.Injective (Q.comapToOriginal inclusion) :=
  Q.comapToOriginal_injective inclusion

include data

/-- Cuspidal-inertia generation makes the induced restriction map onto. -/
theorem restriction_surjective :
    Function.Surjective (Q.comapToOriginal inclusion) :=
  Q.comapToOriginal_surjective_of_cuspidalInertia inclusion
    data.subgraphInertia data.ambientInertia data.inertiaRestriction
    data.inertiaRestriction_surjective data.ambientInertia_generates
    data.inertia_square

/-- IUT II, Corollary 2.5(i)'s restriction isomorphism, derived from the
cuspidal-inertia data. -/
noncomputable def restrictionMulEquiv :
    (Q.comap inclusion).Carrier ≃* Q.Carrier :=
  Q.comapMulEquivOfCuspidalInertia inclusion
    data.subgraphInertia data.ambientInertia data.inertiaRestriction
    data.inertiaRestriction_surjective data.ambientInertia_generates
    data.inertia_square

@[simp]
theorem restrictionMulEquiv_projection
    (source : (Q.comap inclusion).numerator) :
    data.restrictionMulEquiv
        ((Q.comap inclusion).projection source) =
      Q.projection (Q.comapNumeratorHom inclusion source) :=
  rfl

/-- Hausdorff/compact realizations upgrade the source isomorphism to a
topological group equivalence. -/
noncomputable def restrictionContinuousMulEquiv
    [CompactSpace (Q.comap inclusion).Carrier]
    [T2Space Q.Carrier] :
    (Q.comap inclusion).Carrier ≃ₜ* Q.Carrier :=
  Q.comapContinuousMulEquivOfCuspidalInertia inclusion
    data.subgraphInertia data.ambientInertia data.inertiaRestriction
    data.inertiaRestriction_surjective data.ambientInertia_generates
    data.inertia_square

end SourceIUTIICorollary25CuspidalRestriction

namespace GlobalLTorsionCoverInput

variable
  {l : PrimeGeFive}
  {F : Type u} [Field F]
  {curve : PuncturedEllipticCurve F}
  {orbicurves : SignQuotientOrbicurveData F curve}
  (data : GlobalLTorsionCoverInput l orbicurves)

/-- The composite arithmetic quotient `Pi_X -> Pi_X^ell` in *Etale Theta*,
Section 2. -/
def standardThetaToEllipticHom :
    orbicurves.xFundamentalGroups.arithmetic.group →*
      data.piEll :=
  data.arithmeticElliptic.quotient.comp
    data.arithmeticTheta.arithmeticQuotient

/-- The arithmetic-to-elliptic quotient as a continuous homomorphism. -/
def standardThetaToEllipticContinuousHom :
    TopologicalGroupCat.ofProfinite
        orbicurves.xFundamentalGroups.arithmetic.group ⟶
      TopologicalGroupCat.ofProfinite data.piEll where
  toMonoidHom := data.standardThetaToEllipticHom
  continuous_toFun :=
    data.arithmeticEllipticQuotientContinuous.comp
      data.arithmeticThetaQuotientContinuous

/-- The arithmetic theta quotient is an open quotient map of profinite
groups. -/
theorem arithmeticThetaQuotient_isOpenQuotientMap :
    IsOpenQuotientMap data.arithmeticTheta.arithmeticQuotient :=
  profiniteSurjectiveHom_isOpenQuotientMap
    data.arithmeticTheta.arithmeticQuotient
    data.arithmeticThetaQuotientContinuous
    data.arithmeticTheta.arithmeticQuotient_surjective

/-- Hence the arithmetic theta-quotient kernel is closed. -/
theorem arithmeticThetaQuotient_ker_isClosed :
    IsClosed
      ((data.arithmeticTheta.arithmeticQuotient.ker :
          Subgroup orbicurves.xFundamentalGroups.arithmetic.group) :
        Set orbicurves.xFundamentalGroups.arithmetic.group) := by
  change IsClosed
    {source |
      data.arithmeticTheta.arithmeticQuotient source = 1}
  exact isClosed_singleton.preimage
    data.arithmeticThetaQuotientContinuous

/-- The arithmetic theta-to-elliptic quotient is an open quotient map of
profinite groups. -/
theorem arithmeticEllipticQuotient_isOpenQuotientMap :
    IsOpenQuotientMap data.arithmeticElliptic.quotient :=
  profiniteSurjectiveHom_isOpenQuotientMap
    data.arithmeticElliptic.quotient
    data.arithmeticEllipticQuotientContinuous
    data.arithmeticElliptic.quotient_surjective

/-- Hence the arithmetic theta-center kernel is closed. -/
theorem arithmeticEllipticQuotient_ker_isClosed :
    IsClosed
      ((data.arithmeticElliptic.quotient.ker : Subgroup data.piTheta) :
        Set data.piTheta) := by
  change IsClosed
    {source | data.arithmeticElliptic.quotient source = 1}
  exact isClosed_singleton.preimage
    data.arithmeticEllipticQuotientContinuous

/-- The arithmetic theta quotient exact sequence is exact in topological
groups, with its geometric term carrying the certified profinite quotient
topology. -/
theorem arithmeticThetaQuotientExact_isSES :
    TopologicalGroup.IsSES
      data.arithmeticTheta.quotientExact.inclusion
      data.arithmeticTheta.quotientExact.projection :=
  profiniteExactSequence_isSES
    (A :=
      data.geometricLowerCentralTopology.modLThetaQuotientProfiniteGrp)
    (B := data.piTheta)
    (C := orbicurves.absoluteGalois)
    data.arithmeticTheta.quotientExact.inclusion
    data.arithmeticTheta.quotientExact.projection
    data.arithmeticThetaInclusionContinuous
    data.arithmeticThetaProjectionContinuous
    data.arithmeticTheta.quotientExact.inclusion_injective
    data.arithmeticTheta.quotientExact.projection_surjective
    data.arithmeticTheta.quotientExact.exact

/-- The arithmetic elliptic quotient exact sequence is exact in topological
groups, with its geometric term carrying the certified profinite quotient
topology. -/
theorem arithmeticEllipticQuotientExact_isSES :
    TopologicalGroup.IsSES
      data.arithmeticElliptic.exact.inclusion
      data.arithmeticElliptic.exact.projection :=
  profiniteExactSequence_isSES
    (A :=
      data.geometricLowerCentralTopology.modLEllipticAbelianizationProfiniteGrp)
    (B := data.piEll)
    (C := orbicurves.absoluteGalois)
    data.arithmeticElliptic.exact.inclusion
    data.arithmeticElliptic.exact.projection
    data.arithmeticEllipticInclusionContinuous
    data.arithmeticEllipticProjectionContinuous
    data.arithmeticElliptic.exact.inclusion_injective
    data.arithmeticElliptic.exact.projection_surjective
    data.arithmeticElliptic.exact.exact

/-- The theta-root cover group is the inverse image of the selected Galois
section in `Pi_X^ell`.  Thus it is derived from the theta-root splitting, rather
than supplied as an unrelated subgroup. -/
noncomputable def standardThetaRootArithmeticSubgroup :
    Subgroup orbicurves.xFundamentalGroups.arithmetic.group :=
  Subgroup.comap data.standardThetaToEllipticHom
    data.thetaRoot.thetaRootSubgroup

/-- The theta-root arithmetic subgroup is open. -/
theorem standardThetaRootArithmeticSubgroup_isOpen :
    IsOpen
      ((data.standardThetaRootArithmeticSubgroup :
          Subgroup orbicurves.xFundamentalGroups.arithmetic.group) :
        Set orbicurves.xFundamentalGroups.arithmetic.group) := by
  exact data.thetaRootSubgroup_isOpen.preimage
    data.standardThetaToEllipticContinuousHom.continuous_toFun

/-- The standard-type theta-root cover as a literal ambient subquotient with
trivial denominator. -/
noncomputable def standardThetaRootSubquotient :
    SourceTopologicalSubquotient
      (TopologicalGroupCat.ofProfinite
        orbicurves.xFundamentalGroups.arithmetic.group) where
  numerator := data.standardThetaRootArithmeticSubgroup
  denominator := ⊥
  denominator_normal := inferInstance

/-- Quotienting the theta-root cover subgroup by the trivial denominator
recovers that same topological group. -/
noncomputable def standardThetaRootContinuousMulEquiv :
    data.standardThetaRootSubquotient.Carrier ≃ₜ*
      data.standardThetaRootArithmeticSubgroup := by
  unfold SourceTopologicalSubquotient.Carrier
  unfold standardThetaRootSubquotient
  exact
    { toMulEquiv := QuotientGroup.quotientBot
      continuous_toFun := by
        apply Continuous.quotient_lift
        exact continuous_id
      continuous_invFun := QuotientGroup.continuous_mk }

/-- The actual integral `l * Delta^Theta` subquotient on the geometric
fundamental group.  Both numerator and denominator are derived from the
lower-central theta quotient, not from its finite exponent-`l` residue. -/
noncomputable def standardGeometricLDeltaThetaSubquotient
    (data : GlobalLTorsionCoverInput l orbicurves) :
    SourceProfiniteSubquotient
      (TopologicalGroupCat.ofProfinite
        orbicurves.xFundamentalGroups.geometric.group) where
  numerator :=
    EtaleTheta.LDeltaThetaNumerator
      orbicurves.xFundamentalGroups.geometric.group l.value
  numerator_isClosed :=
    data.geometricLowerCentralTopology.lDeltaThetaNumerator_isClosed
  denominator :=
    EtaleTheta.LDeltaThetaDenominator
      orbicurves.xFundamentalGroups.geometric.group l.value
  denominator_normal :=
    EtaleTheta.lDeltaThetaDenominator_normal
      orbicurves.xFundamentalGroups.geometric.group l.value
  denominator_isClosed :=
    data.geometricLowerCentralTopology.lDeltaThetaDenominator_isClosed
  profiniteModel :=
    data.geometricLowerCentralTopology.lDeltaThetaProfiniteGrp
  carrierEquiv :=
    data.geometricLowerCentralTopology.lDeltaThetaSubquotientContinuousMulEquiv

/-- The literal geometric source subquotient is the integral
`l * Delta^Theta` subgroup by the first isomorphism theorem. -/
noncomputable def standardGeometricLDeltaThetaMulEquiv :
    data.standardGeometricLDeltaThetaSubquotient.Carrier ≃ₜ*
      data.geometricLowerCentralTopology.lDeltaThetaProfiniteGrp :=
  data.standardGeometricLDeltaThetaSubquotient.carrierEquiv

/-- The numerator of the integral theta subquotient transported into the
arithmetic fundamental group along `Delta_X -> Pi_X`. -/
noncomputable def standardArithmeticLDeltaThetaNumerator :
    Subgroup orbicurves.xFundamentalGroups.arithmetic.group :=
  Subgroup.map
    data.arithmeticTheta.originalExact.inclusion
    (EtaleTheta.LDeltaThetaNumerator
      orbicurves.xFundamentalGroups.geometric.group l.value)

/-- The transported lower-central denominator inside the transported
arithmetic numerator. -/
noncomputable def standardArithmeticLDeltaThetaDenominator :
    Subgroup data.standardArithmeticLDeltaThetaNumerator :=
  Subgroup.map
    (data.arithmeticTheta.originalExact.inclusion.subgroupMap
      (EtaleTheta.LDeltaThetaNumerator
        orbicurves.xFundamentalGroups.geometric.group l.value))
    (EtaleTheta.LDeltaThetaDenominator
      orbicurves.xFundamentalGroups.geometric.group l.value)

instance standardArithmeticLDeltaThetaDenominator_normal :
    data.standardArithmeticLDeltaThetaDenominator.Normal := by
  exact
    (EtaleTheta.lDeltaThetaDenominator_normal
        orbicurves.xFundamentalGroups.geometric.group l.value).map
      (data.arithmeticTheta.originalExact.inclusion.subgroupMap
        (EtaleTheta.LDeltaThetaNumerator
          orbicurves.xFundamentalGroups.geometric.group l.value))
      (MonoidHom.subgroupMap_surjective
        data.arithmeticTheta.originalExact.inclusion
        (EtaleTheta.LDeltaThetaNumerator
          orbicurves.xFundamentalGroups.geometric.group l.value))

/-- The original geometric inclusion is continuous; its algebraic spelling in
`ArithmeticThetaQuotientData` is definitionally pinned to the profinite exact
sequence by `originalExact_eq`. -/
theorem continuous_standardOriginalGeometricInclusion :
    Continuous data.arithmeticTheta.originalExact.inclusion := by
  rw [data.originalExact_eq]
  exact
    orbicurves.xFundamentalGroups.exactSequence.inclusion.hom.continuous_toFun

/-- The arithmetic numerator is closed because it is the compact image of the
closed geometric numerator. -/
theorem standardArithmeticLDeltaThetaNumerator_isClosed :
    IsClosed
      ((data.standardArithmeticLDeltaThetaNumerator :
          Subgroup orbicurves.xFundamentalGroups.arithmetic.group) :
        Set orbicurves.xFundamentalGroups.arithmetic.group) := by
  change IsClosed
    (data.arithmeticTheta.originalExact.inclusion ''
      ((EtaleTheta.LDeltaThetaNumerator
          orbicurves.xFundamentalGroups.geometric.group l.value :
        Subgroup orbicurves.xFundamentalGroups.geometric.group) :
        Set orbicurves.xFundamentalGroups.geometric.group))
  exact
    (data.geometricLowerCentralTopology.lDeltaThetaNumerator_isClosed.isCompact.image
      data.continuous_standardOriginalGeometricInclusion).isClosed

/-- The transported denominator is closed in the transported numerator. -/
theorem standardArithmeticLDeltaThetaDenominator_isClosed :
    IsClosed
      ((data.standardArithmeticLDeltaThetaDenominator :
          Subgroup data.standardArithmeticLDeltaThetaNumerator) :
        Set data.standardArithmeticLDeltaThetaNumerator) := by
  let sourceNumerator :=
    EtaleTheta.LDeltaThetaNumerator
      orbicurves.xFundamentalGroups.geometric.group l.value
  letI : CompactSpace sourceNumerator :=
    data.geometricLowerCentralTopology.lDeltaThetaNumerator_isClosed
      |>.isClosedEmbedding_subtypeVal.compactSpace
  let inclusion :=
    data.arithmeticTheta.originalExact.inclusion.subgroupMap sourceNumerator
  have inclusion_continuous : Continuous inclusion := by
    apply Continuous.subtype_mk
    exact data.continuous_standardOriginalGeometricInclusion.comp
      continuous_subtype_val
  change IsClosed
    (inclusion ''
      ((EtaleTheta.LDeltaThetaDenominator
          orbicurves.xFundamentalGroups.geometric.group l.value :
        Subgroup sourceNumerator) : Set sourceNumerator))
  exact
    (data.geometricLowerCentralTopology.lDeltaThetaDenominator_isClosed.isCompact.image
      inclusion_continuous).isClosed

/-- Injectivity of the geometric fundamental-group inclusion transports the
geometric numerator isomorphically onto the arithmetic numerator. -/
noncomputable def standardLDeltaThetaNumeratorEquiv :
    EtaleTheta.LDeltaThetaNumerator
        orbicurves.xFundamentalGroups.geometric.group l.value ≃*
      data.standardArithmeticLDeltaThetaNumerator :=
  Subgroup.equivMapOfInjective
    (EtaleTheta.LDeltaThetaNumerator
      orbicurves.xFundamentalGroups.geometric.group l.value)
    data.arithmeticTheta.originalExact.inclusion
    data.arithmeticTheta.originalExact.inclusion_injective

/-- The numerator transport is a homeomorphism between closed subgroups of
the geometric and arithmetic profinite groups. -/
noncomputable def standardLDeltaThetaNumeratorContinuousMulEquiv :
    EtaleTheta.LDeltaThetaNumerator
        orbicurves.xFundamentalGroups.geometric.group l.value ≃ₜ*
      data.standardArithmeticLDeltaThetaNumerator := by
  letI : CompactSpace
      (EtaleTheta.LDeltaThetaNumerator
        orbicurves.xFundamentalGroups.geometric.group l.value) :=
    data.geometricLowerCentralTopology.lDeltaThetaNumerator_isClosed
      |>.isClosedEmbedding_subtypeVal.compactSpace
  let equivalence := data.standardLDeltaThetaNumeratorEquiv
  have continuous_equivalence : Continuous equivalence := by
    apply Continuous.subtype_mk
    exact data.continuous_standardOriginalGeometricInclusion.comp
      continuous_subtype_val
  exact
    { toMulEquiv := equivalence
      continuous_toFun := continuous_equivalence
      continuous_invFun :=
        Continuous.continuous_symm_of_equiv_compact_to_t2
          continuous_equivalence }

theorem standardLDeltaThetaNumeratorEquiv_maps_denominator :
    Subgroup.map
        data.standardLDeltaThetaNumeratorEquiv.toMonoidHom
        (EtaleTheta.LDeltaThetaDenominator
          orbicurves.xFundamentalGroups.geometric.group l.value) =
      data.standardArithmeticLDeltaThetaDenominator := by
  rfl

/-- The induced quotient equivalence transports the geometric subquotient
exactly onto its arithmetic image. -/
noncomputable def standardGeometricToArithmeticLDeltaThetaMulEquiv :
    data.standardGeometricLDeltaThetaSubquotient.Carrier ≃ₜ*
      (data.standardArithmeticLDeltaThetaNumerator ⧸
        data.standardArithmeticLDeltaThetaDenominator) := by
  letI : CompactSpace
      (EtaleTheta.LDeltaThetaNumerator
        orbicurves.xFundamentalGroups.geometric.group l.value) :=
    data.geometricLowerCentralTopology.lDeltaThetaNumerator_isClosed
      |>.isClosedEmbedding_subtypeVal.compactSpace
  letI : CompactSpace
      data.standardGeometricLDeltaThetaSubquotient.Carrier := by
    exact Homeomorph.compactSpace
      data.standardGeometricLDeltaThetaSubquotient.carrierEquiv.toHomeomorph.symm
  letI : IsClosed
      ((data.standardArithmeticLDeltaThetaDenominator :
          Subgroup data.standardArithmeticLDeltaThetaNumerator) :
        Set data.standardArithmeticLDeltaThetaNumerator) :=
    data.standardArithmeticLDeltaThetaDenominator_isClosed
  let equivalence :
      data.standardGeometricLDeltaThetaSubquotient.Carrier ≃*
        (data.standardArithmeticLDeltaThetaNumerator ⧸
          data.standardArithmeticLDeltaThetaDenominator) := by
    unfold SourceProfiniteSubquotient.Carrier
    unfold standardGeometricLDeltaThetaSubquotient
    exact QuotientGroup.congr
      (EtaleTheta.LDeltaThetaDenominator
        orbicurves.xFundamentalGroups.geometric.group l.value)
      data.standardArithmeticLDeltaThetaDenominator
      data.standardLDeltaThetaNumeratorEquiv
      data.standardLDeltaThetaNumeratorEquiv_maps_denominator
  have continuous_equivalence : Continuous equivalence := by
    apply (QuotientGroup.isQuotientMap_mk
      (EtaleTheta.LDeltaThetaDenominator
        orbicurves.xFundamentalGroups.geometric.group l.value)).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp
      data.standardLDeltaThetaNumeratorContinuousMulEquiv.continuous_toFun
  exact
    { toMulEquiv := equivalence
      continuous_toFun := continuous_equivalence
      continuous_invFun :=
        Continuous.continuous_symm_of_equiv_compact_to_t2
          continuous_equivalence }

/-- The integral `l * Delta^Theta` subquotient as a closed profinite
subquotient of the arithmetic fundamental group.  Its two subgroups are images
of the exact geometric numerator and denominator. -/
noncomputable def standardArithmeticLDeltaThetaSubquotient :
    SourceProfiniteSubquotient
      (TopologicalGroupCat.ofProfinite
        orbicurves.xFundamentalGroups.arithmetic.group) where
  numerator := data.standardArithmeticLDeltaThetaNumerator
  numerator_isClosed :=
    data.standardArithmeticLDeltaThetaNumerator_isClosed
  denominator := data.standardArithmeticLDeltaThetaDenominator
  denominator_normal :=
    data.standardArithmeticLDeltaThetaDenominator_normal
  denominator_isClosed :=
    data.standardArithmeticLDeltaThetaDenominator_isClosed
  profiniteModel :=
    data.geometricLowerCentralTopology.lDeltaThetaProfiniteGrp
  carrierEquiv :=
    data.standardGeometricToArithmeticLDeltaThetaMulEquiv.symm.trans
      data.standardGeometricLDeltaThetaMulEquiv

/-- Thus the arithmetic image subquotient is canonically the same integral
`l * Delta^Theta` coefficient group. -/
noncomputable def standardArithmeticLDeltaThetaMulEquiv :
    data.standardArithmeticLDeltaThetaSubquotient.Carrier ≃ₜ*
      data.geometricLowerCentralTopology.lDeltaThetaProfiniteGrp :=
  data.standardArithmeticLDeltaThetaSubquotient.carrierEquiv

@[simp]
theorem standardGeometricToArithmeticLDeltaThetaMulEquiv_projection
    (source :
      data.standardGeometricLDeltaThetaSubquotient.numerator) :
    data.standardGeometricToArithmeticLDeltaThetaMulEquiv
        (data.standardGeometricLDeltaThetaSubquotient.projection source) =
      data.standardArithmeticLDeltaThetaSubquotient.projection
        (data.standardLDeltaThetaNumeratorEquiv source) :=
  rfl

/-- The numerator of the finite mod-`l` theta-center residue: the kernel of
the composite arithmetic-to-elliptic quotient. -/
def standardModLThetaCenterNumerator :
    Subgroup orbicurves.xFundamentalGroups.arithmetic.group :=
  data.standardThetaToEllipticHom.ker

/-- Its denominator is the arithmetic exponent-`l` theta-quotient kernel,
restricted to the numerator. -/
def standardModLThetaCenterDenominator :
    Subgroup data.standardModLThetaCenterNumerator :=
  Subgroup.comap
    data.standardModLThetaCenterNumerator.subtype
    data.arithmeticTheta.arithmeticQuotient.ker

instance standardModLThetaCenterDenominator_normal :
    data.standardModLThetaCenterDenominator.Normal := by
  change
    (Subgroup.comap
      data.standardModLThetaCenterNumerator.subtype
      data.arithmeticTheta.arithmeticQuotient.ker).Normal
  infer_instance

/-- The finite theta-center residue
`ker(Pi_X -> Pi_X^ell) / ker(Pi_X -> Pi_X^Theta)`.  This quotient is not the
integral subgroup `l * Delta^Theta` constructed above. -/
def standardModLThetaCenterSubquotient :
    SourceTopologicalSubquotient
      (TopologicalGroupCat.ofProfinite
        orbicurves.xFundamentalGroups.arithmetic.group) where
  numerator := data.standardModLThetaCenterNumerator
  denominator := data.standardModLThetaCenterDenominator
  denominator_normal :=
    data.standardModLThetaCenterDenominator_normal

/-- The numerator is exactly the inverse image of the embedded geometric theta
center. This is the theta-center kernel equation expressed back in the original
arithmetic group. -/
theorem standardModLThetaCenterNumerator_eq_center_preimage :
    data.standardModLThetaCenterNumerator =
      Subgroup.comap
        data.arithmeticTheta.arithmeticQuotient
        ((EtaleTheta.ModLThetaCenter
            orbicurves.xFundamentalGroups.geometric.group l.value).map
          data.arithmeticTheta.quotientExact.inclusion) := by
  ext source
  change
    data.arithmeticElliptic.quotient
        (data.arithmeticTheta.arithmeticQuotient source) = 1 ↔
      data.arithmeticTheta.arithmeticQuotient source ∈
        (EtaleTheta.ModLThetaCenter
            orbicurves.xFundamentalGroups.geometric.group l.value).map
          data.arithmeticTheta.quotientExact.inclusion
  rw [← data.arithmeticElliptic.thetaCenter_kernel]
  exact MonoidHom.mem_ker

/-- The numerator maps onto the theta-center image, i.e. the kernel of
`Pi_X^Theta -> Pi_X^ell`. -/
def standardModLThetaCenterProjection :
    data.standardModLThetaCenterNumerator →*
      data.arithmeticElliptic.quotient.ker where
  toFun source :=
    ⟨data.arithmeticTheta.arithmeticQuotient source.1, source.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one data.arithmeticTheta.arithmeticQuotient
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul data.arithmeticTheta.arithmeticQuotient first.1 second.1

@[simp]
theorem standardModLThetaCenterProjection_apply
    (source : data.standardModLThetaCenterNumerator) :
    (data.standardModLThetaCenterProjection source).1 =
      data.arithmeticTheta.arithmeticQuotient source.1 :=
  rfl

/-- Its kernel is exactly the denominator of the source subquotient. -/
theorem standardModLThetaCenterProjection_ker :
    data.standardModLThetaCenterProjection.ker =
      data.standardModLThetaCenterDenominator := by
  ext source
  simp only [MonoidHom.mem_ker]
  change
    data.standardModLThetaCenterProjection source = 1 ↔
      data.arithmeticTheta.arithmeticQuotient source.1 = 1
  exact Subtype.ext_iff

/-- Surjectivity follows from surjectivity of the arithmetic theta quotient. -/
theorem standardModLThetaCenterProjection_surjective :
    Function.Surjective data.standardModLThetaCenterProjection := by
  intro target
  obtain ⟨source, hsource⟩ :=
    data.arithmeticTheta.arithmeticQuotient_surjective target.1
  refine ⟨⟨source, ?_⟩, ?_⟩
  · change
      data.arithmeticElliptic.quotient
          (data.arithmeticTheta.arithmeticQuotient source) = 1
    rw [hsource]
    exact target.2
  · apply Subtype.ext
    exact hsource

/-- The quotient map from the numerator to the theta-center image is continuous. -/
theorem continuous_standardModLThetaCenterProjection :
    Continuous data.standardModLThetaCenterProjection := by
  apply Continuous.subtype_mk
  exact data.arithmeticThetaQuotientContinuous.comp
    continuous_subtype_val

/-- The theta-center numerator is closed in the profinite arithmetic group. -/
theorem standardModLThetaCenterNumerator_isClosed :
    IsClosed
      ((data.standardModLThetaCenterNumerator :
          Subgroup orbicurves.xFundamentalGroups.arithmetic.group) :
        Set orbicurves.xFundamentalGroups.arithmetic.group) := by
  change IsClosed
    { source |
      data.standardThetaToEllipticHom source = 1 }
  exact isClosed_singleton.preimage
    data.standardThetaToEllipticContinuousHom.continuous_toFun

/-- The closed theta-center numerator is compact. -/
noncomputable instance standardModLThetaCenterNumeratorCompactSpace :
    CompactSpace data.standardModLThetaCenterNumerator :=
  data.standardModLThetaCenterNumerator_isClosed
    |>.isClosedEmbedding_subtypeVal.compactSpace

/-- Its quotient by the arithmetic theta kernel is compact. -/
noncomputable instance standardModLThetaCenterSubquotientCompactSpace :
    CompactSpace data.standardModLThetaCenterSubquotient.Carrier := by
  letI : CompactSpace data.standardModLThetaCenterSubquotient.numerator := by
    change CompactSpace data.standardModLThetaCenterNumerator
    infer_instance
  exact Quotient.compactSpace

/-- The first isomorphism theorem identifies the literal subquotient with the
theta-center image in the arithmetic theta quotient. -/
noncomputable def standardModLThetaCenterMulEquivCenterImage :
    data.standardModLThetaCenterSubquotient.Carrier ≃*
      data.arithmeticElliptic.quotient.ker := by
  unfold SourceTopologicalSubquotient.Carrier
  unfold standardModLThetaCenterSubquotient
  change
    data.standardModLThetaCenterNumerator ⧸
        data.standardModLThetaCenterDenominator ≃*
      data.arithmeticElliptic.quotient.ker
  exact
    (QuotientGroup.quotientMulEquivOfEq
      data.standardModLThetaCenterProjection_ker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective
          data.standardModLThetaCenterProjection
          data.standardModLThetaCenterProjection_surjective)

/-- Continuity of the first-isomorphism-theorem map follows by testing it on
the quotient projection. -/
theorem continuous_standardModLThetaCenterMulEquivCenterImage :
    Continuous data.standardModLThetaCenterMulEquivCenterImage := by
  apply
    (QuotientGroup.isQuotientMap_mk
      data.standardModLThetaCenterSubquotient.denominator).continuous_iff.mpr
  change Continuous
    (data.standardModLThetaCenterMulEquivCenterImage ∘
      QuotientGroup.mk)
  convert data.continuous_standardModLThetaCenterProjection using 1

/-- The first-isomorphism-theorem identification is an equivalence of
topological groups. -/
noncomputable def standardModLThetaCenterContinuousMulEquivCenterImage :
    data.standardModLThetaCenterSubquotient.Carrier ≃ₜ*
      data.arithmeticElliptic.quotient.ker where
  toMulEquiv := data.standardModLThetaCenterMulEquivCenterImage
  continuous_toFun :=
    data.continuous_standardModLThetaCenterMulEquivCenterImage
  continuous_invFun :=
    Continuous.continuous_symm_of_equiv_compact_to_t2
      data.continuous_standardModLThetaCenterMulEquivCenterImage

@[simp]
theorem standardModLThetaCenterContinuousMulEquivCenterImage_projection
    (source : data.standardModLThetaCenterSubquotient.numerator) :
    data.standardModLThetaCenterContinuousMulEquivCenterImage
        (data.standardModLThetaCenterSubquotient.projection source) =
      data.standardModLThetaCenterProjection source :=
  rfl

/-- The embedded geometric theta center maps into the arithmetic theta-center
kernel. -/
def standardThetaCenterImageHom :
    EtaleTheta.ModLThetaCenter
        orbicurves.xFundamentalGroups.geometric.group l.value →*
      data.arithmeticElliptic.quotient.ker where
  toFun center := by
    refine
      ⟨data.arithmeticTheta.quotientExact.inclusion center.1, ?_⟩
    have hsquare :
        data.arithmeticElliptic.exact.inclusion
            (EtaleTheta.modLThetaToElliptic
              orbicurves.xFundamentalGroups.geometric.group
              l.value center.1) =
          data.arithmeticElliptic.quotient
            (data.arithmeticTheta.quotientExact.inclusion center.1) :=
      DFunLike.congr_fun
        data.arithmeticElliptic.geometric_square center.1
    change
      data.arithmeticElliptic.quotient
          (data.arithmeticTheta.quotientExact.inclusion center.1) = 1
    rw [← hsquare, center.2]
    exact map_one data.arithmeticElliptic.exact.inclusion
  map_one' := by
    apply Subtype.ext
    exact map_one data.arithmeticTheta.quotientExact.inclusion
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul data.arithmeticTheta.quotientExact.inclusion first.1 second.1

/-- The geometric theta center embeds bijectively onto the arithmetic
theta-center kernel. -/
theorem standardThetaCenterImageHom_bijective :
    Function.Bijective data.standardThetaCenterImageHom := by
  constructor
  · intro first second heq
    apply Subtype.ext
    apply data.arithmeticTheta.quotientExact.inclusion_injective
    exact congrArg Subtype.val heq
  · intro target
    have target_mem :
        target.1 ∈
          (EtaleTheta.ModLThetaCenter
              orbicurves.xFundamentalGroups.geometric.group l.value).map
            data.arithmeticTheta.quotientExact.inclusion := by
      rw [← data.arithmeticElliptic.thetaCenter_kernel]
      exact target.2
    obtain ⟨center, center_mem, hcenter⟩ := target_mem
    refine ⟨⟨center, center_mem⟩, ?_⟩
    apply Subtype.ext
    exact hcenter

/-- The center-image kernel is the actual finite geometric theta center of the
exponent-`l` quotient, not merely an isomorphic cyclic group. -/
noncomputable def standardThetaCenterImageEquiv :
    EtaleTheta.ModLThetaCenter
        orbicurves.xFundamentalGroups.geometric.group l.value ≃*
      data.arithmeticElliptic.quotient.ker :=
  MulEquiv.ofBijective data.standardThetaCenterImageHom
    data.standardThetaCenterImageHom_bijective

/-- Combining both exact identifications gives the source subquotient's
canonical algebraic equivalence with the derived geometric theta center. -/
noncomputable def standardModLThetaCenterMulEquiv :
    data.standardModLThetaCenterSubquotient.Carrier ≃*
      EtaleTheta.ModLThetaCenter
        orbicurves.xFundamentalGroups.geometric.group l.value :=
  data.standardModLThetaCenterMulEquivCenterImage.trans
    data.standardThetaCenterImageEquiv.symm

end GlobalLTorsionCoverInput

/-- Continuous automorphisms of a topological group. -/
abbrev ContinuousAutomorphism (G : TopologicalGroupCat.{u}) :=
  G ≃ₜ* G

namespace ContinuousAutomorphism

variable (G : TopologicalGroupCat.{u})

instance : Mul (ContinuousAutomorphism G) :=
  ⟨fun f g => g.trans f⟩

instance : One (ContinuousAutomorphism G) :=
  ⟨_root_.ContinuousMulEquiv.refl G⟩

instance : Inv (ContinuousAutomorphism G) :=
  ⟨fun f => f.symm⟩

instance : Group (ContinuousAutomorphism G) :=
  Group.ofLeftAxioms
    (fun _ _ _ => by
      apply _root_.ContinuousMulEquiv.ext
      intro
      rfl)
    (fun _ => by
      apply _root_.ContinuousMulEquiv.ext
      intro
      rfl)
    (fun f => by
      apply _root_.ContinuousMulEquiv.ext
      intro x
      exact f.left_inv x)

/-- Conjugation by a group element as a continuous automorphism. -/
def inner (g : G) : ContinuousAutomorphism G where
  toMulEquiv := MulAut.conj g
  continuous_toFun :=
    (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun :=
    (continuous_const.mul continuous_id).mul continuous_const

@[simp]
theorem inner_apply (g x : G) :
    inner G g x = g * x * g⁻¹ :=
  rfl

/-- Inner automorphisms form the range of the conjugation homomorphism. -/
def innerHom : G →* ContinuousAutomorphism G where
  toFun := inner G
  map_one' := by
    apply _root_.ContinuousMulEquiv.ext
    intro x
    change (1 : G) * x * (1 : G)⁻¹ = x
    simp
  map_mul' g h := by
    apply _root_.ContinuousMulEquiv.ext
    intro x
    change
      (g * h) * x * (g * h)⁻¹ =
        g * (h * x * h⁻¹) * g⁻¹
    simp [mul_assoc]

/-- The range of the conjugation homomorphism is a normal subgroup. -/
theorem inner_range_normal :
    (innerHom G).range.Normal := by
  constructor
  intro innerAutomorphism hinner automorphism
  rcases hinner with ⟨g, rfl⟩
  refine ⟨automorphism g, ?_⟩
  apply _root_.ContinuousMulEquiv.ext
  intro x
  change
    automorphism g * x * (automorphism g)⁻¹ =
      automorphism
        (g * automorphism.symm x * g⁻¹)
  simp

instance : (innerHom G).range.Normal :=
  inner_range_normal G

/-- The exact inner-automorphism subgroup, i.e. the range of conjugation. -/
def innerSubgroup : Subgroup (ContinuousAutomorphism G) :=
  (innerHom G).range

/-- The continuous outer automorphism group `Aut_cont(G) / Inn(G)`. -/
abbrev Outer :=
  ContinuousAutomorphism G ⧸ innerSubgroup G

/-- Transport a continuous automorphism through a topological-group isomorphism. -/
def transport
    {H : TopologicalGroupCat.{u}}
    (e : G ≃ₜ* H) (f : ContinuousAutomorphism G) :
    ContinuousAutomorphism H :=
  e.symm.trans (f.trans e)

@[simp]
theorem transport_apply
    {H : TopologicalGroupCat.{u}}
    (e : G ≃ₜ* H) (f : ContinuousAutomorphism G) (x : H) :
    transport G e f x = e (f (e.symm x)) :=
  rfl

end ContinuousAutomorphism

/--
A subgroup of `Out(G)`, represented by its full inverse image in
`Aut_cont(G)`.  Containment of all inner automorphisms is precisely the
condition for such a full inverse image.
-/
structure ContinuousOuterSubgroup (G : TopologicalGroupCat.{u}) where
  automorphisms : Subgroup (ContinuousAutomorphism G)
  inner_le :
    ContinuousAutomorphism.innerSubgroup G ≤ automorphisms

/-- Two subgroups are conjugate by an element of a specified subgroup. -/
def SubgroupsConjugateBy
    {G : Type u} [Group G]
    (conjugators first second : Subgroup G) : Prop :=
  ∃ g : conjugators,
    second =
      first.map (MulAut.conj (g : G)).toMonoidHom

namespace SubgroupsConjugateBy

variable {G : Type u} [Group G]
variable {C H K L : Subgroup G}

theorem refl (H : Subgroup G) :
    SubgroupsConjugateBy C H H := by
  refine ⟨⟨1, C.one_mem⟩, ?_⟩
  ext x
  simp

theorem symm (h : SubgroupsConjugateBy C H K) :
    SubgroupsConjugateBy C K H := by
  rcases h with ⟨g, rfl⟩
  refine ⟨⟨(g : G)⁻¹, C.inv_mem g.property⟩, ?_⟩
  ext x
  simp [Subgroup.mem_map, mul_assoc]

end SubgroupsConjugateBy

/--
The ordered triple underlying a mod-`N` mono-theta environment in EtTh,
Definition 2.13(ii).

The cyclic kernel is explicit, and the theta-section collection is derived
from the image of an actual continuous injective section.
-/
structure SourceMonoThetaEnvironmentData
    (N : ℕ+) (G : TopologicalGroupCat.{u}) where
  outerSymmetries : ContinuousOuterSubgroup G
  cyclotome : Subgroup G
  cyclotomeLabelEquiv :
    cyclotome ≃*
      EtaleTheta.LTorsionLabel N.val
  thetaSectionDomain : TopologicalGroupCat.{u}
  thetaSection : thetaSectionDomain ⟶ G
  thetaSection_injective :
    Function.Injective thetaSection.toMonoidHom

namespace SourceMonoThetaEnvironmentData

variable {N : ℕ+} {G : TopologicalGroupCat.{u}}

/-- The representative subgroup determined by the image of the theta section. -/
def thetaSectionSubgroup
    (E : SourceMonoThetaEnvironmentData N G) :
    Subgroup G :=
  E.thetaSection.toMonoidHom.range

/-- The `mu_N`-conjugacy class of theta-section images. -/
def thetaSectionClass
    (E : SourceMonoThetaEnvironmentData N G) :
    Set (Subgroup G) :=
  { H | SubgroupsConjugateBy E.cyclotome E.thetaSectionSubgroup H }

theorem thetaSectionSubgroup_mem_class
    (E : SourceMonoThetaEnvironmentData N G) :
    E.thetaSectionSubgroup ∈ E.thetaSectionClass :=
  SubgroupsConjugateBy.refl E.thetaSectionSubgroup

end SourceMonoThetaEnvironmentData

/--
The additional geometric generators of a model mono-theta environment.
Their images, together with all inner automorphisms, generate the prescribed
inverse image of `D_Y` in the continuous automorphism group.
-/
structure SourceModelMonoThetaEnvironment
    (N : ℕ+) (G : TopologicalGroupCat.{u}) where
  data : SourceMonoThetaEnvironmentData N G
  unitSymmetryGroup : TopologicalGroupCat.{u}
  deckSymmetryGroup : TopologicalGroupCat.{u}
  unitOuterAction :
    unitSymmetryGroup →*
      ContinuousAutomorphism G
  deckOuterAction :
    deckSymmetryGroup →*
      ContinuousAutomorphism G
  outerSymmetries_generated :
    data.outerSymmetries.automorphisms =
      ContinuousAutomorphism.innerSubgroup G ⊔
        unitOuterAction.range ⊔
          deckOuterAction.range

/--
An isomorphism from an abstract mono-theta triple to a model triple.  Each
compatibility is stated on the actual group isomorphism rather than by an
unrelated equivalence of labels.
-/
structure SourceMonoThetaEnvironmentRealization
    {N : ℕ+}
    {G H : TopologicalGroupCat.{u}}
    (source : SourceMonoThetaEnvironmentData N G)
    (target : SourceMonoThetaEnvironmentData N H) where
  groupIso : G ≃ₜ* H
  outerSymmetries_iff :
    ∀ f : ContinuousAutomorphism G,
      f ∈ source.outerSymmetries.automorphisms ↔
        ContinuousAutomorphism.transport G groupIso f ∈
          target.outerSymmetries.automorphisms
  cyclotome_iff :
    ∀ x : G,
      x ∈ source.cyclotome ↔
        groupIso x ∈ target.cyclotome
  thetaSections_compatible :
    SubgroupsConjugateBy
      target.cyclotome
      (source.thetaSectionSubgroup.map
        groupIso.toMulEquiv.toMonoidHom)
      target.thetaSectionSubgroup

/--
A mod-`N` mono-theta environment: an abstract ordered triple together with
the model realization required by EtTh, Definition 2.13(ii).
-/
structure SourceMonoThetaEnvironment
    (N : ℕ+) (G : TopologicalGroupCat.{u}) where
  data : SourceMonoThetaEnvironmentData N G
  modelGroup : TopologicalGroupCat.{u}
  model : SourceModelMonoThetaEnvironment N modelGroup
  realization :
    SourceMonoThetaEnvironmentRealization data model.data

/--
Positive moduli ordered in the direction of the transition arrows:
`M' ≤ M` means that `M` divides `M'`, hence the system has a map from the
mod-`M'` object to the mod-`M` object.
-/
structure MonoThetaModulus where
  modulus : ℕ+

namespace MonoThetaModulus

instance : Preorder MonoThetaModulus where
  le M' M := M.modulus.val ∣ M'.modulus.val
  le_refl _ := dvd_rfl
  le_trans _ _ _ h₁ h₂ := dvd_trans h₂ h₁

end MonoThetaModulus

/--
A projective system of mono-theta environments as used in IUT II,
Definition 2.7.

The group maps form an actual functor.  Surjectivity and compatibility with
the cyclic kernels and theta-section conjugacy classes record the reduction
behavior of the EtTh transition morphisms.  Compatibility of the full outer
actions with the induced moduli remains a separate source obligation.
-/
structure SourceMonoThetaProjectiveSystem where
  groupDiagram :
    MonoThetaModulus ⥤ TopologicalGroupCat.{u}
  environment :
    ∀ M : MonoThetaModulus,
      SourceMonoThetaEnvironment M.modulus
        (groupDiagram.obj M)
  transition_surjective :
    ∀ {M' M : MonoThetaModulus} (f : M' ⟶ M),
      Function.Surjective
        (groupDiagram.map f).toMonoidHom
  transition_cyclotome :
    ∀ {M' M : MonoThetaModulus} (f : M' ⟶ M),
      Subgroup.map
          (groupDiagram.map f).toMonoidHom
          (environment M').data.cyclotome =
        (environment M).data.cyclotome
  transition_thetaSections :
    ∀ {M' M : MonoThetaModulus} (f : M' ⟶ M),
      SubgroupsConjugateBy
        (environment M).data.cyclotome
        (Subgroup.map
          (groupDiagram.map f).toMonoidHom
          (environment M').data.thetaSectionSubgroup)
        (environment M).data.thetaSectionSubgroup
  inverseLimitCone : Limits.Cone groupDiagram
  inverseLimitCone_isLimit :
    Limits.IsLimit inverseLimitCone

namespace SourceMonoThetaProjectiveSystem

/-- The topological inverse-limit group `Pi_(MTheta_*)`. -/
def inverseLimit (S : SourceMonoThetaProjectiveSystem.{u}) :
    TopologicalGroupCat.{u} :=
  S.inverseLimitCone.pt

/-- The canonical projection from the inverse limit to a finite level. -/
def projection
    (S : SourceMonoThetaProjectiveSystem.{u})
    (M : MonoThetaModulus) :
    S.inverseLimit ⟶ S.groupDiagram.obj M :=
  S.inverseLimitCone.π.app M

theorem projection_naturality
    (S : SourceMonoThetaProjectiveSystem.{u})
    {M' M : MonoThetaModulus} (f : M' ⟶ M) :
    S.projection M' ≫ S.groupDiagram.map f =
      S.projection M :=
  S.inverseLimitCone.w f

end SourceMonoThetaProjectiveSystem

/--
IUT II, Definition 2.7(i): the inverse-limit group, its natural map to the
ambient fundamental group, the exterior cyclotome as its exact kernel, and
the tempered subgroup as its exact image.
-/
structure SourceIUTIIDefinition27PartI where
  system : SourceMonoThetaProjectiveSystem.{u}
  ambientFundamentalGroup : TopologicalGroupCat.{u}
  toAmbient :
    system.inverseLimit ⟶ ambientFundamentalGroup
  exteriorCyclotome :
    Subgroup system.inverseLimit
  kernel_eq_exteriorCyclotome :
    toAmbient.toMonoidHom.ker =
      exteriorCyclotome
  temperedSubgroup :
    Subgroup ambientFundamentalGroup
  range_eq_temperedSubgroup :
    toAmbient.toMonoidHom.range =
      temperedSubgroup

namespace SourceIUTIIDefinition27PartI

/-- The inverse image of an ambient subgroup in the mono-theta inverse limit. -/
def inverseImage
    (partI : SourceIUTIIDefinition27PartI.{u})
    (subgroup : Subgroup partI.ambientFundamentalGroup) :
    Subgroup partI.system.inverseLimit :=
  Subgroup.comap partI.toAmbient.toMonoidHom subgroup

/-- The inverse image equipped with its induced topological-group structure. -/
def inverseImageGroup
    (partI : SourceIUTIIDefinition27PartI.{u})
    (subgroup : Subgroup partI.ambientFundamentalGroup) :
    TopologicalGroupCat.{u} :=
  TopologicalGroupCat.ofSubgroup
    partI.system.inverseLimit
    (partI.inverseImage subgroup)

/-- The natural map from an inverse-image group to the ambient fundamental group. -/
def inverseImageToAmbient
    (partI : SourceIUTIIDefinition27PartI.{u})
    (subgroup : Subgroup partI.ambientFundamentalGroup) :
    partI.inverseImageGroup subgroup ⟶
      partI.ambientFundamentalGroup :=
  partI.toAmbient.comp
    (TopologicalGroupCat.subgroupInclusion
      partI.system.inverseLimit
      (partI.inverseImage subgroup))

/--
Restriction of the exterior cyclotome to an inverse-image group.  Its
numerator is the actual inverse image of the exterior cyclotome and its
denominator is trivial.
-/
def exteriorCyclotomeRestriction
    (partI : SourceIUTIIDefinition27PartI.{u})
    (subgroup : Subgroup partI.ambientFundamentalGroup) :
    SourceTopologicalSubquotient
      (partI.inverseImageGroup subgroup) where
  numerator :=
    Subgroup.comap
      (TopologicalGroupCat.subgroupInclusion
        partI.system.inverseLimit
        (partI.inverseImage subgroup)).toMonoidHom
      partI.exteriorCyclotome
  denominator := ⊥
  denominator_normal := inferInstance

/-- Restrict an ambient subquotient to one Definition 2.7 inverse-image group. -/
def restrictAmbientSubquotient
    (partI : SourceIUTIIDefinition27PartI.{u})
    (subgroup : Subgroup partI.ambientFundamentalGroup)
    (Q :
      SourceTopologicalSubquotient
        partI.ambientFundamentalGroup) :
    SourceTopologicalSubquotient
      (partI.inverseImageGroup subgroup) :=
  Q.comap (partI.inverseImageToAmbient subgroup)

end SourceIUTIIDefinition27PartI

/--
IUT II, Definition 2.7(ii): nested inverse-image groups, the four indicated
subquotients of the smaller inverse image, and restricted cyclotomic rigidity.

The ambient nested groups and their inverse images are not duplicated as
fields: the inverse images are computed through the homomorphism of
Definition 2.7(i).  The exterior cyclotome is restricted directly from the
kernel in part (i); the other three subquotients are pulled back from actual
ambient subquotients.  Constructing those ambient subquotients from IUT II,
Proposition 1.4 and Corollary 2.5 remains part of the source construction.
-/
structure SourceIUTIIDefinition27PartII
    (partI : SourceIUTIIDefinition27PartI.{u}) where
  wideAmbientSubgroup :
    Subgroup partI.ambientFundamentalGroup
  narrowAmbientSubgroup :
    Subgroup partI.ambientFundamentalGroup
  narrow_le_wide :
    narrowAmbientSubgroup ≤ wideAmbientSubgroup
  wide_le_tempered :
    wideAmbientSubgroup ≤ partI.temperedSubgroup
  ambientLDeltaThetaSubquotient :
    SourceProfiniteSubquotient
      partI.ambientFundamentalGroup
  ambientRestrictedTemperedSubquotient :
    SourceTopologicalSubquotient
      partI.ambientFundamentalGroup
  ambientLocalGaloisSubquotient :
    SourceTopologicalSubquotient
      partI.ambientFundamentalGroup
  cyclotomicRigidity :
    (partI.restrictAmbientSubquotient
      narrowAmbientSubgroup
      ambientLDeltaThetaSubquotient.toTopologicalSubquotient).Carrier ≃ₜ*
    (partI.exteriorCyclotomeRestriction
      narrowAmbientSubgroup).Carrier

namespace SourceIUTIIDefinition27PartII

variable
  {partI : SourceIUTIIDefinition27PartI.{u}}
  (partII : SourceIUTIIDefinition27PartII partI)

/-- The wider inverse-image group in the mono-theta inverse limit. -/
def wideInverseImage :
    Subgroup partI.system.inverseLimit :=
  partI.inverseImage partII.wideAmbientSubgroup

/-- The narrower inverse-image group in the mono-theta inverse limit. -/
def narrowInverseImage :
    Subgroup partI.system.inverseLimit :=
  partI.inverseImage partII.narrowAmbientSubgroup

/-- The exterior cyclotome restricted from the kernel in Definition 2.7(i). -/
def exteriorCyclotomeSubquotient :
    SourceTopologicalSubquotient
      (partI.inverseImageGroup
        partII.narrowAmbientSubgroup) :=
  partI.exteriorCyclotomeRestriction
    partII.narrowAmbientSubgroup

/-- The `(l · Delta_Theta)` ambient subquotient restricted to the narrow group. -/
def lDeltaThetaSubquotient :
    SourceTopologicalSubquotient
      (partI.inverseImageGroup
        partII.narrowAmbientSubgroup) :=
  partI.restrictAmbientSubquotient
    partII.narrowAmbientSubgroup
    partII.ambientLDeltaThetaSubquotient.toTopologicalSubquotient

/-- The indicated tempered subquotient restricted to the narrow group. -/
def restrictedTemperedSubquotient :
    SourceTopologicalSubquotient
      (partI.inverseImageGroup
        partII.narrowAmbientSubgroup) :=
  partI.restrictAmbientSubquotient
    partII.narrowAmbientSubgroup
    partII.ambientRestrictedTemperedSubquotient

/-- The local Galois subquotient restricted to the narrow group. -/
def localGaloisSubquotient :
    SourceTopologicalSubquotient
      (partI.inverseImageGroup
        partII.narrowAmbientSubgroup) :=
  partI.restrictAmbientSubquotient
    partII.narrowAmbientSubgroup
    partII.ambientLocalGaloisSubquotient

theorem narrowInverseImage_le_wide :
    partII.narrowInverseImage ≤
      partII.wideInverseImage :=
  Subgroup.comap_mono partII.narrow_le_wide

/-- The stored rigidity isomorphism has the derived restricted subquotients as endpoints. -/
def cyclotomicRigidity_source :
    partII.lDeltaThetaSubquotient.Carrier ≃ₜ*
      partII.exteriorCyclotomeSubquotient.Carrier :=
  partII.cyclotomicRigidity

end SourceIUTIIDefinition27PartII

end Iut
