/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Kummer-faithfulness predicates and group-theoretic lemmas

Absolute Anabelian Topics III, Definition 1.5, quantifies over every finite
extension and every semi-abelian variety (or, in the toral variant, every
torus).  This file records those quantifiers independently of the
group-theoretic finite-quotient argument.  The abstract rational-point families
are an explicit boundary until the corresponding algebraic geometry is
formalized; in particular, a theorem about one integral-unit group cannot
inhabit either field-level predicate.
-/

namespace Iut

namespace SourceKummerFaithfulness

universe u

/-- A finite field extension used by the source-level Definition 1.5
quantifiers. -/
structure FiniteExtension (K : Type u) [Field K] where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra K carrier]
  [finiteDimensional : FiniteDimensional K carrier]

attribute [instance] FiniteExtension.field FiniteExtension.algebra
  FiniteExtension.finiteDimensional

/-- A rational point is infinitely divisible when it lies in the image of
multiplication by every positive integer. -/
def InfinitelyDivisible
    {A : Type u} [AddCommGroup A] (point : A) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ antecedent : A, n • antecedent = point

/-- Definition 1.5(a) for one rational-point group. -/
def HasTrivialInfinitelyDivisibleIntersection
    (A : Type u) [AddCommGroup A] : Prop :=
  ∀ point : A, InfinitelyDivisible point → point = 0

/-- The typed semi-abelian/rational-point boundary needed to state Definition
1.5.  Constructing this family from actual semi-abelian varieties is a separate
algebraic-geometric obligation. -/
structure SemiAbelianRationalPointFamily
    (K : Type u) [Field K] where
  variety : FiniteExtension K → Type u
  rationalPoints : {L : FiniteExtension K} → variety L → Type u
  rationalPointsAddCommGroup :
    ∀ {L : FiniteExtension K} (A : variety L),
      AddCommGroup (rationalPoints A)

/-- The typed torus/rational-point boundary needed to state the toral variant
of Definition 1.5.  It is deliberately distinct from the semi-abelian family,
so the two remaining generality obligations cannot be conflated. -/
structure TorusRationalPointFamily
    (K : Type u) [Field K] where
  torus : FiniteExtension K → Type u
  rationalPoints : {L : FiniteExtension K} → torus L → Type u
  rationalPointsAddCommGroup :
    ∀ {L : FiniteExtension K} (A : torus L),
      AddCommGroup (rationalPoints A)

/-- Absolute Anabelian Topics III, Definition 1.5(a): for every finite
extension and every semi-abelian variety, the rational-point group has no
nonzero infinitely divisible point. -/
def KummerFaithful
    (K : Type u) [Field K]
    (family : SemiAbelianRationalPointFamily K) : Prop :=
  ∀ (L : FiniteExtension K) (A : family.variety L),
    @HasTrivialInfinitelyDivisibleIntersection
      (family.rationalPoints A) (family.rationalPointsAddCommGroup A)

/-- Absolute Anabelian Topics III, Definition 1.5(a), restricted to tori over
every finite extension. -/
def TorallyKummerFaithful
    (K : Type u) [Field K]
    (family : TorusRationalPointFamily K) : Prop :=
  ∀ (L : FiniteExtension K) (A : family.torus L),
    @HasTrivialInfinitelyDivisibleIntersection
      (family.rationalPoints A) (family.rationalPointsAddCommGroup A)

/-- A Kummer map together with the standard characterization of its kernel by
infinitely divisible points.  Injectivity is intentionally not stored. -/
structure AdditiveKummerMap
    (A C : Type u) [AddCommGroup A] [AddCommGroup C] where
  hom : A →+ C
  map_eq_zero_iff_infinitelyDivisible :
    ∀ point : A, hom point = 0 ↔ InfinitelyDivisible point

/-- Definition 1.5(a) derives the equivalent Kummer-map injectivity condition
of Definition 1.5(b). -/
theorem AdditiveKummerMap.injective_of_trivial_infinitelyDivisible
    {A C : Type u} [AddCommGroup A] [AddCommGroup C]
    (kummerMap : AdditiveKummerMap A C)
    (trivialIntersection : HasTrivialInfinitelyDivisibleIntersection A) :
    Function.Injective kummerMap.hom := by
  intro first second hequal
  have difference_map_eq_zero : kummerMap.hom (first - second) = 0 := by
    rw [map_sub, hequal, sub_self]
  have difference_eq_zero : first - second = 0 :=
    trivialIntersection (first - second)
      ((kummerMap.map_eq_zero_iff_infinitelyDivisible _).mp
        difference_map_eq_zero)
  exact sub_eq_zero.mp difference_eq_zero

/-- A multiplicative Kummer map together with the standard characterization
of its kernel by elements admitting roots of every positive degree.
Injectivity is intentionally not stored. -/
structure MultiplicativeKummerMap
    (G C : Type u) [CommGroup G] [CommGroup C] where
  hom : G →* C
  map_eq_one_iff_roots :
    ∀ value : G,
      hom value = 1 ↔
        ∀ n : ℕ, 0 < n → ∃ root : G, root ^ n = value

/-- Root rigidity derives multiplicative Kummer-map injectivity. -/
theorem MultiplicativeKummerMap.injective_of_roots_eq_one
    {G C : Type u} [CommGroup G] [CommGroup C]
    (kummerMap : MultiplicativeKummerMap G C)
    (rootRigidity :
      ∀ value : G,
        (∀ n : ℕ, 0 < n → ∃ root : G, root ^ n = value) →
          value = 1) :
    Function.Injective kummerMap.hom := by
  intro first second hequal
  have quotient_map_eq_one :
      kummerMap.hom (first * second⁻¹) = 1 := by
    rw [map_mul, map_inv, hequal, mul_inv_cancel]
  have quotient_eq_one : first * second⁻¹ = 1 :=
    rootRigidity (first * second⁻¹)
      ((kummerMap.map_eq_one_iff_roots _).mp quotient_map_eq_one)
  exact eq_of_mul_inv_eq_one quotient_eq_one

/-- A residually finite group has no nontrivial element with roots of all degrees. -/
theorem eq_one_of_roots_of_residuallyFinite
    {G : Type u} [Group G] [_root_.Group.ResiduallyFinite G]
    (x : G)
    (roots : ∀ n : ℕ, 0 < n → ∃ y : G, y ^ n = x) :
    x = 1 := by
  apply _root_.Group.eq_one_iff_forall_finiteIndexNormalSubroup x
  intro H
  let quotient := G ⧸ H.toSubgroup
  have quotientFinite : Finite quotient := inferInstance
  obtain ⟨root, hroot⟩ :=
    roots (Nat.card quotient) Nat.card_pos
  change x ∈ H.toSubgroup
  rw [← QuotientGroup.eq_one_iff]
  rw [← hroot, QuotientGroup.mk_pow]
  exact pow_card_eq_one'

/-- Every compact totally disconnected topological group is residually finite. -/
theorem residuallyFinite_of_profinite
    {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] :
    _root_.Group.ResiduallyFinite G := by
  apply
    _root_.Group.residuallyFinite_iff_exists_finiteIndexNormalSubgroup.mpr
  intro x hx
  obtain ⟨H, hH⟩ :=
    _root_.ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (isClosed_singleton.isOpen_compl : IsOpen ({x}ᶜ : Set G))
      (by simpa [eq_comm] using hx)
  exact
    ⟨H.toFiniteIndexNormalSubgroup,
      fun hmem => (hH hmem) rfl⟩

/-- The finite-quotient root-rigidity argument for a profinite group.  This is
one group-level input to Definition 1.5(a), not the complete field-level
semi-abelian or toral assertion. -/
theorem eq_one_of_roots_in_profinite
    {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (x : G)
    (roots : ∀ n : ℕ, 0 < n → ∃ y : G, y ^ n = x) :
    x = 1 := by
  letI : _root_.Group.ResiduallyFinite G :=
    residuallyFinite_of_profinite
  exact eq_one_of_roots_of_residuallyFinite x roots

end SourceKummerFaithfulness

end Iut
