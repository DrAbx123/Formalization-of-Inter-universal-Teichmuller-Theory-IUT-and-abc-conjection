/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceSplitKummerFrobenioid
import Mathlib.Analysis.Complex.Circle
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Archimedean torsion-quotient system from IUT II Definition 4.9(v)

IUT II, Definition 4.9(v), replaces the archimedean split Frobenioid by an
inductive system indexed by a multiplicatively cofinal subset of `N >= 1`.
On units, the system consists of the circle quotients by `N`-torsion, with
compatible surjections from the original compact factor and an indeterminacy
given by inversion.

This file constructs that unit-level system as an actual functor of topological
groups. It includes its quotient topology, exact kernels, continuous transition
maps, arbitrary cofinal restrictions, and the two compatible orientations. It
also proves that every cofinal restriction is a final functor, constructs the
exact split topological monoid at each quotient stage, and states the
structure-preserving boundary for the corresponding reconstructed split
Frobenioid system. It does not yet derive the stages or their transition
functors from the model-Frobenioid reconstruction theorem.
-/

namespace Iut

open CategoryTheory

namespace SourceArchimedeanKummerSystem

noncomputable section

/-- The units of the `N`-torsion quotient at an archimedean place. -/
abbrev UnitQuotient (N : ℕ+) :=
  Circle ⧸ (powMonoidHom (α := Circle) N.val).ker

/-- The `N`-torsion subgroup is closed in the circle. -/
theorem rootsOfUnity_isClosed (N : ℕ+) :
    IsClosed (((powMonoidHom (α := Circle) N.val).ker : Subgroup Circle) : Set Circle) := by
  change IsClosed {unit : Circle | unit ^ N.val = 1}
  exact isClosed_eq (continuous_id.pow N.val) continuous_const

instance (N : ℕ+) :
    IsClosed (((powMonoidHom (α := Circle) N.val).ker : Subgroup Circle) : Set Circle) :=
  rootsOfUnity_isClosed N

/-- The canonical surjection from the compact factor to its `N`-torsion quotient. -/
def quotientMap (N : ℕ+) : Circle →* UnitQuotient N :=
  QuotientGroup.mk' (powMonoidHom (α := Circle) N.val).ker

/-- The quotient map with its source topological-group structure retained. -/
def continuousQuotientMap (N : ℕ+) : Circle →ₜ* UnitQuotient N where
  toMonoidHom := quotientMap N
  continuous_toFun := QuotientGroup.continuous_mk

/-- The canonical map realizes the quotient topology, not only the group quotient. -/
theorem continuousQuotientMap_isOpenQuotientMap (N : ℕ+) :
    IsOpenQuotientMap (continuousQuotientMap N) :=
  QuotientGroup.isOpenQuotientMap_mk

theorem quotientMap_surjective (N : ℕ+) :
    Function.Surjective (quotientMap N) :=
  QuotientGroup.mk'_surjective _

/-- The kernel of the canonical surjection is exactly the `N`-torsion. -/
theorem quotientMap_ker (N : ℕ+) :
    (quotientMap N).ker = (powMonoidHom (α := Circle) N.val).ker :=
  QuotientGroup.ker_mk' _

/-- `mu_N` is contained in `mu_M` whenever `N` divides `M`. -/
theorem rootsOfUnity_le_of_dvd
    (N M : ℕ+) (hNM : N ∣ M) :
    (powMonoidHom (α := Circle) N.val).ker ≤
      (powMonoidHom (α := Circle) M.val).ker := by
  rcases hNM with ⟨K, rfl⟩
  intro unit hunit
  change unit ^ N.val = 1 at hunit
  change unit ^ (N.val * K.val) = 1
  rw [pow_mul, hunit, one_pow]

/-- The transition `O^(times-mu_N) → O^(times-mu_M)` for `N ∣ M`. -/
def transition (N M : ℕ+) (hNM : N ∣ M) :
    UnitQuotient N →* UnitQuotient M :=
  QuotientGroup.map
    (powMonoidHom (α := Circle) N.val).ker
    (powMonoidHom (α := Circle) M.val).ker
    (MonoidHom.id Circle)
    (by simpa using rootsOfUnity_le_of_dvd N M hNM)

/-- The transition is a continuous homomorphism of quotient topological groups. -/
def continuousTransition (N M : ℕ+) (hNM : N ∣ M) :
    UnitQuotient N →ₜ* UnitQuotient M where
  toMonoidHom := transition N M hNM
  continuous_toFun := by
    rw [← (QuotientGroup.isOpenQuotientMap_mk
      (N := (powMonoidHom (α := Circle) N.val).ker)).continuous_comp_iff]
    exact QuotientGroup.continuous_mk

@[simp]
theorem continuousTransition_mk
    (N M : ℕ+) (hNM : N ∣ M) (unit : Circle) :
    continuousTransition N M hNM (continuousQuotientMap N unit) =
      continuousQuotientMap M unit :=
  rfl

@[simp]
theorem transition_mk
    (N M : ℕ+) (hNM : N ∣ M) (unit : Circle) :
    transition N M hNM (quotientMap N unit) = quotientMap M unit :=
  rfl

/-- Every transition in the archimedean system is surjective. -/
theorem transition_surjective (N M : ℕ+) (hNM : N ∣ M) :
    Function.Surjective (transition N M hNM) := by
  intro value
  induction value using QuotientGroup.induction_on with
  | _ unit =>
      exact ⟨quotientMap N unit, transition_mk N M hNM unit⟩

/-- The transition kernel is the image of `mu_M` modulo `mu_N`. -/
theorem transition_ker (N M : ℕ+) (hNM : N ∣ M) :
    (transition N M hNM).ker =
      Subgroup.map (quotientMap N)
        (powMonoidHom (α := Circle) M.val).ker := by
  simpa [transition, quotientMap] using
    QuotientGroup.ker_map
      (N := (powMonoidHom (α := Circle) N.val).ker)
      (M := (powMonoidHom (α := Circle) M.val).ker)
      (MonoidHom.id Circle)
      (by simpa using rootsOfUnity_le_of_dvd N M hNM)

/-- The quotient surjections commute with every transition. -/
theorem transition_comp_quotientMap
    (N M : ℕ+) (hNM : N ∣ M) :
    (transition N M hNM).comp (quotientMap N) = quotientMap M := by
  ext unit
  rfl

/-- Transitions compose as an inductive system over divisibility. -/
theorem transition_comp
    (N M L : ℕ+) (hNM : N ∣ M) (hML : M ∣ L) :
    (transition M L hML).comp (transition N M hNM) =
      transition N L (dvd_trans hNM hML) := by
  ext unit
  rfl

/-- The transition from an index to itself is the identity map. -/
theorem transition_self (N : ℕ+) :
    transition N N (dvd_refl N) = MonoidHom.id (UnitQuotient N) := by
  ext unit
  rfl

/-- Continuous transitions compose as the same divisibility-indexed system. -/
theorem continuousTransition_comp
    (N M L : ℕ+) (hNM : N ∣ M) (hML : M ∣ L) :
    (continuousTransition M L hML).comp (continuousTransition N M hNM) =
      continuousTransition N L (dvd_trans hNM hML) := by
  apply _root_.ContinuousMonoidHom.ext
  intro unit
  exact DFunLike.congr_fun (transition_comp N M L hNM hML) unit

/-- The continuous self-transition is the identity. -/
theorem continuousTransition_self (N : ℕ+) :
    continuousTransition N N (dvd_refl N) =
      _root_.ContinuousMonoidHom.id (UnitQuotient N) := by
  apply _root_.ContinuousMonoidHom.ext
  intro unit
  exact DFunLike.congr_fun (transition_self N) unit

/-- The two orientation choices allowed for the compact archimedean factor. -/
inductive Orientation
  | direct
  | conjugate
  deriving DecidableEq

/-- Direct orientation or the designated continuous reversal `z ↦ z⁻¹`. -/
def orientationAutomorphism : Orientation → (Circle ≃ₜ* Circle)
  | .direct => ContinuousMulEquiv.refl Circle
  | .conjugate =>
      { MulEquiv.inv Circle with
        continuous_toFun := continuous_inv
        continuous_invFun := continuous_inv }

/-- The compatible quotient-surjection system after one orientation choice. -/
def orientedQuotientMap (orientation : Orientation) (N : ℕ+) :
    Circle →* UnitQuotient N :=
  (quotientMap N).comp
    (orientationAutomorphism orientation).toMulEquiv.toMonoidHom

/-- The oriented quotient map as a continuous homomorphism. -/
def continuousOrientedQuotientMap
    (orientation : Orientation) (N : ℕ+) :
    Circle →ₜ* UnitQuotient N :=
  (continuousQuotientMap N).comp
    (orientationAutomorphism orientation : Circle →ₜ* Circle)

/-- The quotient unit group as a packaged topological monoid. -/
def unitQuotientPresentation (N : ℕ+) :
    TopologicalMonoidPresentation.{0} where
  carrier := UnitQuotient N

/-- Every element of the compact quotient group is a unit. -/
theorem unitQuotient_isUnit (N : ℕ+) (value : UnitQuotient N) :
    IsUnit value :=
  isUnit_iff_exists_inv.mpr ⟨value⁻¹, by simp⟩

/-- The compact inclusion into the exact quotient/noncompact product. -/
def quotientCompactInclusion
    (source : SplitTopologicalMonoidPresentation.{0}) (N : ℕ+) :
    ContinuousMonoidHom
      (unitQuotientPresentation N)
      (TopologicalMonoidPresentation.prod
        (unitQuotientPresentation N) source.noncompactFactor) where
  hom :=
    { toFun := fun compact => (compact, 1)
      map_one' := rfl
      map_mul' := by
        intro first second
        apply Prod.ext
        · rfl
        · exact (one_mul 1).symm }
  continuous := continuous_id.prodMk continuous_const

/-- The unchanged noncompact inclusion at a quotient stage. -/
def quotientNoncompactInclusion
    (source : SplitTopologicalMonoidPresentation.{0}) (N : ℕ+) :
    ContinuousMonoidHom
      source.noncompactFactor
      (TopologicalMonoidPresentation.prod
        (unitQuotientPresentation N) source.noncompactFactor) where
  hom :=
    { toFun := fun noncompact => (1, noncompact)
      map_one' := rfl
      map_mul' := by
        intro first second
        apply Prod.ext
        · exact (one_mul 1).symm
        · rfl }
  continuous := continuous_const.prodMk continuous_id

/-- The distinguished noncompact factor of a split topological monoid has no nontrivial units. -/
theorem noncompact_eq_one_of_isUnit
    (source : SplitTopologicalMonoidPresentation.{0})
    (value : source.noncompactFactor.carrier)
    (hvalue : IsUnit value) :
    value = 1 := by
  have hproduct :
      IsUnit ((1, value) :
        source.compactFactor.carrier × source.noncompactFactor.carrier) :=
    Prod.isUnit_iff.mpr ⟨isUnit_one, hvalue⟩
  have htotal :
      IsUnit (source.factorization.toHom (1, value)) :=
    hproduct.map source.factorization.toHom.hom
  obtain ⟨compact, hcompact⟩ :=
    source.every_unit_compact
      (source.factorization.toHom (1, value)) htotal
  have himage :
      source.factorization.toHom (1, value) =
        source.factorization.toHom (compact, 1) := by
    calc
      source.factorization.toHom (1, value) =
          source.compactInclusion compact := hcompact.symm
      _ = source.factorization.toHom (compact, 1) := by
        rw [source.factorization_eq]
        simp
  have hpairs :
      (1, value) =
        (compact, 1) :=
    source.factorization.left_inv.injective himage
  exact congrArg Prod.snd hpairs

/--
The exact split topological monoid obtained by quotienting the compact units by
`mu_N` and leaving the characteristic noncompact factor unchanged.
-/
def quotientSplitTopologicalMonoid
    (source : SplitTopologicalMonoidPresentation.{0}) (N : ℕ+) :
    SplitTopologicalMonoidPresentation.{0} where
  total :=
    TopologicalMonoidPresentation.prod
      (unitQuotientPresentation N) source.noncompactFactor
  compactFactor := unitQuotientPresentation N
  noncompactFactor := source.noncompactFactor
  compactInclusion := quotientCompactInclusion source N
  noncompactInclusion := quotientNoncompactInclusion source N
  compact_isUnit value := by
    change IsUnit ((value, 1) : UnitQuotient N ×
      source.noncompactFactor.carrier)
    exact Prod.isUnit_iff.mpr
      ⟨unitQuotient_isUnit N value, isUnit_one⟩
  every_unit_compact value hvalue := by
    refine ⟨value.1, ?_⟩
    apply Prod.ext
    · rfl
    · exact (noncompact_eq_one_of_isUnit source value.2
        (Prod.isUnit_iff.mp hvalue).2).symm
  factorization :=
    TopologicalMonoidIso.refl
      (TopologicalMonoidPresentation.prod
        (unitQuotientPresentation N) source.noncompactFactor)
  factorization_eq compact noncompact := by
    apply Prod.ext
    · exact (mul_one compact).symm
    · exact (one_mul noncompact).symm

/-- The product transition induced by `mu_N ⊆ mu_M`, with fixed noncompact factor. -/
def quotientSplitTransition
    (source : SplitTopologicalMonoidPresentation.{0})
    (N M : ℕ+) (hNM : N ∣ M) :
    ContinuousMonoidHom
      (quotientSplitTopologicalMonoid source N).total
      (quotientSplitTopologicalMonoid source M).total where
  hom :=
    { toFun := fun value => (transition N M hNM value.1, value.2)
      map_one' := by
        apply Prod.ext
        · exact (transition N M hNM).map_one
        · rfl
      map_mul' := by
        intro first second
        apply Prod.ext
        · exact (transition N M hNM).map_mul first.1 second.1
        · rfl }
  continuous :=
    (continuousTransition N M hNM).continuous.prodMap continuous_id

@[simp]
theorem quotientSplitTransition_apply
    (source : SplitTopologicalMonoidPresentation.{0})
    (N M : ℕ+) (hNM : N ∣ M)
    (value : (quotientSplitTopologicalMonoid source N).total.carrier) :
    quotientSplitTransition source N M hNM value =
      (transition N M hNM value.1, value.2) :=
  rfl

/-- The exact quotient-stage boundary for Definition 4.9(v)'s split Frobenioid. -/
structure FrobenioidStage
    (underlying : ArchimedeanSplitFrobenioidPresentation.{0})
    (N : ℕ+) where
  reconstructed : ArchimedeanSplitFrobenioidPresentation.{0}
  quotientSplittingIso :
    SplitTopologicalMonoidIso
      reconstructed.topologicalSplitting
      (quotientSplitTopologicalMonoid underlying.topologicalSplitting N)
  baseEquivalence :
    CategoryTheory.Equivalence
      reconstructed.frobenioid.frobenioid.baseCategory
      underlying.frobenioid.frobenioid.baseCategory

namespace FrobenioidStage

/-- The complete unit factor of a reconstructed stage is the exact `mu_N` quotient. -/
def compactUnitsIso
    {underlying : ArchimedeanSplitFrobenioidPresentation.{0}}
    {N : ℕ+} (stage : FrobenioidStage underlying N) :
    TopologicalMonoidIso
      stage.reconstructed.topologicalSplitting.compactFactor
      (unitQuotientPresentation N) :=
  stage.quotientSplittingIso.compactFactor

/-- The carrier category of a reconstructed stage. -/
abbrev Carrier
    {underlying : ArchimedeanSplitFrobenioidPresentation.{0}}
    {N : ℕ+} (stage : FrobenioidStage underlying N) :=
  stage.reconstructed.frobenioid.frobenioid.carrier

/-- The divisor base category of a reconstructed stage. -/
abbrev BaseCategory
    {underlying : ArchimedeanSplitFrobenioidPresentation.{0}}
    {N : ℕ+} (stage : FrobenioidStage underlying N) :=
  stage.reconstructed.frobenioid.frobenioid.baseCategory

/-- The divisor monoid at the base of a reconstructed carrier object. -/
abbrev DivisorAt
    {underlying : ArchimedeanSplitFrobenioidPresentation.{0}}
    {N : ℕ+} (stage : FrobenioidStage underlying N)
    (X : Carrier stage) :=
  (stage.reconstructed.frobenioid.frobenioid.preFrobenioid.divisorMonoid.obj
    ((stage.reconstructed.frobenioid.frobenioid.preFrobenioid.base).obj X)).carrier

/-- The rational-function monoid at a reconstructed stage's reference object. -/
abbrev referenceRationalMonoid
    {underlying : ArchimedeanSplitFrobenioidPresentation.{0}}
    {N : ℕ+} (stage : FrobenioidStage underlying N) :=
  stage.reconstructed.frobenioid.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism
    stage.reconstructed.referenceObject

end FrobenioidStage

/--
The actual divisibility-indexed system of reconstructed split Frobenioids in
Definition 4.9(v). The carrier and base functors form strict diagrams, their
reference-object rational monoids form a third strict diagram, and the latter
is required to realize the concrete quotient transition on the compact factor
while fixing the noncompact factor.
-/
structure FrobenioidSystem
    (underlying : ArchimedeanSplitFrobenioidPresentation.{0}) where
  stage : ∀ N : ℕ+, FrobenioidStage underlying N
  carrierTransition :
    ∀ (N M : ℕ+) (_hNM : N ∣ M),
      (stage N).reconstructed.frobenioid.frobenioid.carrier ⥤
        (stage M).reconstructed.frobenioid.frobenioid.carrier
  baseTransition :
    ∀ (N M : ℕ+) (_hNM : N ∣ M),
      (stage N).reconstructed.frobenioid.frobenioid.baseCategory ⥤
        (stage M).reconstructed.frobenioid.frobenioid.baseCategory
  carrier_base_compatible :
    ∀ (N M : ℕ+) (hNM : N ∣ M),
      carrierTransition N M hNM ⋙
          (stage M).reconstructed.frobenioid.frobenioid.preFrobenioid.base =
        (stage N).reconstructed.frobenioid.frobenioid.preFrobenioid.base ⋙
          baseTransition N M hNM
  base_underlying_compatible :
    ∀ (N M : ℕ+) (hNM : N ∣ M),
      baseTransition N M hNM ⋙ (stage M).baseEquivalence.functor =
        (stage N).baseEquivalence.functor
  fsm_compatible :
    ∀ (N M : ℕ+) (hNM : N ∣ M)
      {first second :
        (stage N).reconstructed.frobenioid.frobenioid.baseCategory}
      (map : first ⟶ second),
      (stage N).reconstructed.frobenioid.frobenioid.isFSM map →
        (stage M).reconstructed.frobenioid.frobenioid.isFSM
          ((baseTransition N M hNM).map map)
  divisorTransition :
    ∀ (N M : ℕ+) (_hNM : N ∣ M)
      (X : FrobenioidStage.Carrier (stage N)),
      FrobenioidStage.DivisorAt (stage N) X →+
        FrobenioidStage.DivisorAt (stage M)
          ((carrierTransition N M _hNM).obj X)
  divisor_compatible :
    ∀ (N M : ℕ+) (hNM : N ∣ M)
      {X Y : (stage N).reconstructed.frobenioid.frobenioid.carrier}
      (map : X ⟶ Y),
      divisorTransition N M hNM X
          ((stage N).reconstructed.frobenioid.frobenioid.preFrobenioid.divisor map) =
        (stage M).reconstructed.frobenioid.frobenioid.preFrobenioid.divisor
          ((carrierTransition N M hNM).map map)
  frobeniusDegree_compatible :
    ∀ (N M : ℕ+) (hNM : N ∣ M)
      {X Y : (stage N).reconstructed.frobenioid.frobenioid.carrier}
      (map : X ⟶ Y),
      (stage M).reconstructed.frobenioid.frobenioid.preFrobenioid.frobeniusDegree
          ((carrierTransition N M hNM).map map) =
        (stage N).reconstructed.frobenioid.frobenioid.preFrobenioid.frobeniusDegree map
  referenceIso :
    ∀ (N M : ℕ+) (hNM : N ∣ M),
      (carrierTransition N M hNM).obj
          (stage N).reconstructed.referenceObject ≅
        (stage M).reconstructed.referenceObject
  rationalTransition :
    ∀ (N M : ℕ+) (_hNM : N ∣ M),
      FrobenioidStage.referenceRationalMonoid (stage N) →*
        FrobenioidStage.referenceRationalMonoid (stage M)
  rationalTransition_hom :
    ∀ (N M : ℕ+) (hNM : N ∣ M)
      (value : FrobenioidStage.referenceRationalMonoid (stage N)),
      (rationalTransition N M hNM value).hom =
        (referenceIso N M hNM).inv ≫
          (carrierTransition N M hNM).map value.hom ≫
            (referenceIso N M hNM).hom
  quotient_transition_compatible :
    ∀ (N M : ℕ+) (hNM : N ∣ M)
      (value : FrobenioidStage.referenceRationalMonoid (stage N)),
      (stage M).quotientSplittingIso.total.toHom
          ((stage M).reconstructed.rationalTotalIso
            (rationalTransition N M hNM value)) =
        quotientSplitTransition underlying.topologicalSplitting N M hNM
          ((stage N).quotientSplittingIso.total.toHom
            ((stage N).reconstructed.rationalTotalIso value))
  carrierTransition_self :
    ∀ N,
      carrierTransition N N (dvd_refl N) =
        Functor.id ((stage N).reconstructed.frobenioid.frobenioid.carrier)
  carrierTransition_comp :
    ∀ (N M L : ℕ+) (hNM : N ∣ M) (hML : M ∣ L),
      carrierTransition N M hNM ⋙ carrierTransition M L hML =
        carrierTransition N L (dvd_trans hNM hML)
  baseTransition_self :
    ∀ N,
      baseTransition N N (dvd_refl N) =
        Functor.id ((stage N).reconstructed.frobenioid.frobenioid.baseCategory)
  baseTransition_comp :
    ∀ (N M L : ℕ+) (hNM : N ∣ M) (hML : M ∣ L),
      baseTransition N M hNM ⋙ baseTransition M L hML =
        baseTransition N L (dvd_trans hNM hML)
  rationalTransition_self :
    ∀ N,
      rationalTransition N N (dvd_refl N) =
        MonoidHom.id
          (FrobenioidStage.referenceRationalMonoid (stage N))
  rationalTransition_comp :
    ∀ (N M L : ℕ+) (hNM : N ∣ M) (hML : M ∣ L),
      (rationalTransition M L hML).comp
          (rationalTransition N M hNM) =
        rationalTransition N L (dvd_trans hNM hML)

/-- Every oriented map is an open quotient map, hence a topological surjection. -/
theorem continuousOrientedQuotientMap_isOpenQuotientMap
    (orientation : Orientation) (N : ℕ+) :
    IsOpenQuotientMap (continuousOrientedQuotientMap orientation N) :=
  (continuousQuotientMap_isOpenQuotientMap N).comp
    (orientationAutomorphism orientation).toHomeomorph.isOpenQuotientMap

/-- Every oriented map has kernel exactly `mu_N`. -/
theorem orientedQuotientMap_ker
    (orientation : Orientation) (N : ℕ+) :
    (orientedQuotientMap orientation N).ker =
      (powMonoidHom (α := Circle) N.val).ker := by
  ext unit
  change
    (((orientationAutomorphism orientation unit : Circle) : UnitQuotient N) = 1) ↔
      unit ^ N.val = 1
  rw [QuotientGroup.eq_one_iff]
  cases orientation with
  | direct => rfl
  | conjugate =>
      change unit⁻¹ ^ N.val = 1 ↔ unit ^ N.val = 1
      rw [inv_pow, inv_eq_one]

/-- The orientation choice is compatible across the entire inductive system. -/
theorem transition_comp_orientedQuotientMap
    (orientation : Orientation) (N M : ℕ+) (hNM : N ∣ M) :
    (transition N M hNM).comp (orientedQuotientMap orientation N) =
      orientedQuotientMap orientation M := by
  ext unit
  rfl

/-- The continuously oriented quotient maps commute with every transition. -/
theorem continuousTransition_comp_orientedQuotientMap
    (orientation : Orientation) (N M : ℕ+) (hNM : N ∣ M) :
    (continuousTransition N M hNM).comp
        (continuousOrientedQuotientMap orientation N) =
      continuousOrientedQuotientMap orientation M := by
  ext unit
  rfl

/-- The designated reversal is genuinely nontrivial. -/
theorem orientationAutomorphism_ne
    : orientationAutomorphism .direct ≠ orientationAutomorphism .conjugate := by
  intro equality
  have h := DFunLike.congr_fun equality (Circle.exp (Real.pi / 2))
  change Circle.exp (Real.pi / 2) = (Circle.exp (Real.pi / 2))⁻¹ at h
  have hcoe := congrArg (fun value : Circle => (value : ℂ)) h
  simp only [Circle.coe_exp, Circle.coe_inv] at hcoe
  rw [Complex.ofReal_div] at hcoe
  norm_num at hcoe
  have him := congrArg Complex.im hcoe
  norm_num at him

/-- Positive integers ordered by divisibility, the source indexing category. -/
structure DivisibilityIndex where
  value : ℕ+
  deriving DecidableEq

instance : Preorder DivisibilityIndex where
  le first second := first.value ∣ second.value
  le_refl index := dvd_refl index.value
  le_trans _ _ _ := dvd_trans

@[simp]
theorem divisibilityIndex_le_iff (first second : DivisibilityIndex) :
    first ≤ second ↔ first.value ∣ second.value :=
  Iff.rfl

/-- Divisibility on positive integers is a filtered indexing category. -/
instance divisibilityIndexIsFiltered : IsFiltered DivisibilityIndex where
  cocone_objs first second :=
    ⟨⟨first.value * second.value⟩,
      homOfLE ⟨second.value, rfl⟩,
      homOfLE ⟨first.value, mul_comm _ _⟩, trivial⟩
  cocone_maps {X Y} _ _ :=
    ⟨Y, 𝟙 Y, by subsingleton⟩
  nonempty := ⟨⟨1⟩⟩

/-- A subset cofinal for divisibility in the multiplicative monoid of positive integers. -/
structure MultiplicativelyCofinalSubset where
  carrier : Set ℕ+
  cofinal : ∀ N : ℕ+, ∃ M : ℕ+, M ∈ carrier ∧ N ∣ M

namespace MultiplicativelyCofinalSubset

/-- The divisibility index category cut out by a cofinal subset. -/
abbrev Index (subset : MultiplicativelyCofinalSubset) :=
  { index : DivisibilityIndex // index.value ∈ subset.carrier }

/-- Inclusion of a cofinal indexing category into all positive integers. -/
def indexInclusion (subset : MultiplicativelyCofinalSubset) :
    subset.Index ⥤ DivisibilityIndex :=
  (show Monotone (Subtype.val : subset.Index → DivisibilityIndex) from
    fun _ _ hle => hle).functor

/-- Every positive integer is dominated by an index in a cofinal subset. -/
theorem exists_index_above
    (subset : MultiplicativelyCofinalSubset) (N : DivisibilityIndex) :
    ∃ M : subset.Index, N ≤ M.1 := by
  obtain ⟨M, hM, hNM⟩ := subset.cofinal N.value
  exact ⟨⟨⟨M⟩, hM⟩, hNM⟩

/-- Every multiplicatively cofinal indexing subset is itself filtered. -/
instance indexIsFiltered
    (subset : MultiplicativelyCofinalSubset) :
    IsFiltered subset.Index where
  cocone_objs first second := by
    obtain ⟨upper, hupper, hdiv⟩ :=
      subset.cofinal (first.1.value * second.1.value)
    refine
      ⟨⟨⟨upper⟩, hupper⟩,
        homOfLE (dvd_trans ⟨second.1.value, rfl⟩ hdiv),
        homOfLE (dvd_trans ⟨first.1.value, mul_comm _ _⟩ hdiv),
        trivial⟩
  cocone_maps {X Y} _ _ :=
    ⟨Y, 𝟙 Y, by subsingleton⟩
  nonempty := by
    obtain ⟨upper, hupper, _⟩ := subset.cofinal 1
    exact ⟨⟨⟨upper⟩, hupper⟩⟩

/-- Inclusion of any multiplicatively cofinal subset is a final functor. -/
instance indexInclusionFinal
    (subset : MultiplicativelyCofinalSubset) :
    subset.indexInclusion.Final :=
  Functor.final_of_exists_of_isFiltered subset.indexInclusion
    (fun index => by
      obtain ⟨upper, hupper⟩ := subset.exists_index_above index
      exact ⟨upper, ⟨homOfLE hupper⟩⟩)
    (fun {_index stage} _ _ =>
      ⟨stage, 𝟙 _, by subsingleton⟩)

/--
Restriction to a multiplicatively cofinal subset preserves and reflects the
universal colimit cocone. This is the precise categorical identification of
the systems indexed by distinct cofinal subsets in Definition 4.9(v).
-/
def isColimitEquivRestricted
    (subset : MultiplicativelyCofinalSubset)
    {E : Type u} [Category.{u} E]
    (diagram : DivisibilityIndex ⥤ E)
    (cocone : Limits.Cocone diagram) :
    Limits.IsColimit cocone ≃
      Limits.IsColimit (cocone.whisker subset.indexInclusion) :=
  (Functor.Final.isColimitWhiskerEquiv
    subset.indexInclusion cocone).symm

end MultiplicativelyCofinalSubset

namespace FrobenioidSystem

/-- The carrier categories of the reconstructed split Frobenioids form a functor. -/
def carrierDiagram
    {underlying : ArchimedeanSplitFrobenioidPresentation.{0}}
    (system : FrobenioidSystem underlying) :
    DivisibilityIndex ⥤ Cat.{0, 0} where
  obj index :=
    (system.stage index.value).reconstructed.frobenioid.frobenioid.carrier
  map {first second} arrow :=
    (system.carrierTransition first.value second.value arrow.le).toCatHom
  map_id index := by
    apply Cat.Hom.ext
    exact system.carrierTransition_self index.value
  map_comp first second := by
    apply Cat.Hom.ext
    exact (system.carrierTransition_comp _ _ _ first.le second.le).symm

/-- The unchanged divisor-base categories form the accompanying functor. -/
def baseDiagram
    {underlying : ArchimedeanSplitFrobenioidPresentation.{0}}
    (system : FrobenioidSystem underlying) :
    DivisibilityIndex ⥤ Cat.{0, 0} where
  obj index :=
    (system.stage index.value).reconstructed.frobenioid.frobenioid.baseCategory
  map {first second} arrow :=
    (system.baseTransition first.value second.value arrow.le).toCatHom
  map_id index := by
    apply Cat.Hom.ext
    exact system.baseTransition_self index.value
  map_comp first second := by
    apply Cat.Hom.ext
    exact (system.baseTransition_comp _ _ _ first.le second.le).symm

/-- The reference rational monoids form the quotient transition diagram. -/
def rationalMonoidDiagram
    {underlying : ArchimedeanSplitFrobenioidPresentation.{0}}
    (system : FrobenioidSystem underlying) :
    DivisibilityIndex ⥤ MonCat.{0} where
  obj index :=
    MonCat.of
      (FrobenioidStage.referenceRationalMonoid
        (system.stage index.value))
  map {first second} arrow :=
    MonCat.ofHom
      (system.rationalTransition first.value second.value arrow.le)
  map_id index := by
    apply MonCat.hom_ext
    exact system.rationalTransition_self index.value
  map_comp first second := by
    apply MonCat.hom_ext
    exact (system.rationalTransition_comp _ _ _ first.le second.le).symm

/-- Restriction of the reconstructed carrier-category system to a cofinal subset. -/
def restrictedCarrierDiagram
    {underlying : ArchimedeanSplitFrobenioidPresentation.{0}}
    (system : FrobenioidSystem underlying)
    (subset : MultiplicativelyCofinalSubset) :
    subset.Index ⥤ Cat.{0, 0} :=
  subset.indexInclusion ⋙ carrierDiagram system

/-- Restriction of the reconstructed base-category system to a cofinal subset. -/
def restrictedBaseDiagram
    {underlying : ArchimedeanSplitFrobenioidPresentation.{0}}
    (system : FrobenioidSystem underlying)
    (subset : MultiplicativelyCofinalSubset) :
    subset.Index ⥤ Cat.{0, 0} :=
  subset.indexInclusion ⋙ baseDiagram system

/-- Restriction of the reconstructed rational-monoid system to a cofinal subset. -/
def restrictedRationalMonoidDiagram
    {underlying : ArchimedeanSplitFrobenioidPresentation.{0}}
    (system : FrobenioidSystem underlying)
    (subset : MultiplicativelyCofinalSubset) :
    subset.Index ⥤ MonCat.{0} :=
  subset.indexInclusion ⋙ rationalMonoidDiagram system

end FrobenioidSystem

namespace MultiplicativelyCofinalSubset

/-- The full positive-integer indexing set is multiplicatively cofinal. -/
def all : MultiplicativelyCofinalSubset where
  carrier := Set.univ
  cofinal N := ⟨N, Set.mem_univ N, dvd_refl N⟩

end MultiplicativelyCofinalSubset

/-- A quotient unit group as an actual topological-group object. -/
def unitQuotientObject (N : ℕ+) : TopologicalGroupCat.{0} where
  toFundamentalGroup :=
    { carrier := UnitQuotient N
      group := inferInstance
      topology := inferInstance
      isTopologicalGroup := inferInstance
      topologyKind := .abstract }

/-- The compact archimedean factor as a topological-group object. -/
def circleObject : TopologicalGroupCat.{0} where
  toFundamentalGroup :=
    { carrier := Circle
      group := inferInstance
      topology := inferInstance
      isTopologicalGroup := inferInstance
      topologyKind := .abstract }

/-- The actual divisibility-indexed inductive system of topological unit quotients. -/
def unitQuotientDiagram : DivisibilityIndex ⥤ TopologicalGroupCat.{0} where
  obj index := unitQuotientObject index.value
  map {first second} arrow :=
    continuousTransition first.value second.value arrow.le
  map_id index := by
    change continuousTransition index.value index.value (dvd_refl index.value) =
      _root_.ContinuousMonoidHom.id (UnitQuotient index.value)
    exact continuousTransition_self index.value
  map_comp first second := by
    change
      continuousTransition _ _ (dvd_trans first.le second.le) =
        (continuousTransition _ _ second.le).comp
          (continuousTransition _ _ first.le)
    exact (continuousTransition_comp _ _ _ first.le second.le).symm

/-- Each orientation gives one compatible system of quotient surjections. -/
def orientedQuotientNaturalTransformation (orientation : Orientation) :
    (Functor.const DivisibilityIndex).obj circleObject ⟶ unitQuotientDiagram where
  app index := continuousOrientedQuotientMap orientation index.value
  naturality {first second} arrow := by
    apply _root_.ContinuousMonoidHom.ext
    intro unit
    rfl

/-- Restriction of the unit system to any multiplicatively cofinal subset. -/
def restrictedUnitQuotientDiagram
    (subset : MultiplicativelyCofinalSubset) :
    subset.Index ⥤ TopologicalGroupCat.{0} :=
  subset.indexInclusion ⋙ unitQuotientDiagram

/-- The compatible oriented surjections on an arbitrary cofinal subsystem. -/
def restrictedOrientedQuotientNaturalTransformation
    (subset : MultiplicativelyCofinalSubset) (orientation : Orientation) :
    (Functor.const subset.Index).obj circleObject ⟶
      restrictedUnitQuotientDiagram subset where
  app index := continuousOrientedQuotientMap orientation index.1.value
  naturality {first second} arrow := by
    apply _root_.ContinuousMonoidHom.ext
    intro unit
    rfl

end

end SourceArchimedeanKummerSystem

end Iut
