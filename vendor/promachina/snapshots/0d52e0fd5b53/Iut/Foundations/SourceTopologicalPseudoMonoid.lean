/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceMonoThetaEnvironment
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.GroupTheory.Divisible
import Mathlib.GroupTheory.Torsion
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Maps.OpenQuotient
import Mathlib.Topology.Separation.Hausdorff

/-!
# Topological pseudo-monoids and continuous group actions

This module formalizes the convention on topological pseudo-monoids in IUT I,
Section 0.  A pseudo-monoid is represented by its image in the ambient
topological abelian group.  Its multiplication is defined precisely on the
pairs whose ambient product remains in that image; in particular, the carrier
is not required to contain the ambient identity or to be closed under every
product.
-/

open CategoryTheory

namespace Iut

universe u

/--
A topological pseudo-monoid in the sense of IUT I, Section 0, represented by
the image of its topological embedding into an ambient topological abelian
group.
-/
structure SourceTopologicalPseudoMonoid where
  ambient : Type u
  [ambientCommGroup : CommGroup ambient]
  [ambientTopology : TopologicalSpace ambient]
  [ambientTopologicalGroup : IsTopologicalGroup ambient]
  carrierSet : Set ambient

namespace SourceTopologicalPseudoMonoid

attribute [instance]
  ambientCommGroup ambientTopology ambientTopologicalGroup

/-- The pseudo-monoid carrier with the topology induced from its embedding. -/
abbrev Carrier (P : SourceTopologicalPseudoMonoid.{u}) :=
  { value : P.ambient // value ∈ P.carrierSet }

/-- The carrier inclusion is the topological embedding required by the paper. -/
theorem carrier_isEmbedding (P : SourceTopologicalPseudoMonoid.{u}) :
    Topology.IsEmbedding ((↑) : P.Carrier → P.ambient) :=
  Topology.IsEmbedding.subtypeVal

/-- The exact domain on which the pseudo-monoid multiplication is defined. -/
abbrev MultiplicationDomain (P : SourceTopologicalPseudoMonoid.{u}) :=
  { pair : P.Carrier × P.Carrier //
      pair.1.1 * pair.2.1 ∈ P.carrierSet }

/-- Multiplication obtained by restricting ambient multiplication to its domain. -/
def partialMul
    (P : SourceTopologicalPseudoMonoid.{u})
    (input : P.MultiplicationDomain) : P.Carrier :=
  ⟨input.1.1.1 * input.1.2.1, input.2⟩

@[simp]
theorem partialMul_value
    (P : SourceTopologicalPseudoMonoid.{u})
    (input : P.MultiplicationDomain) :
    (P.partialMul input).1 = input.1.1.1 * input.1.2.1 := rfl

/-- The restricted multiplication in a topological pseudo-monoid is continuous. -/
theorem continuous_partialMul
    (P : SourceTopologicalPseudoMonoid.{u}) :
    Continuous P.partialMul := by
  apply Continuous.subtype_mk
  fun_prop

/-- The partial multiplication is commutative on its exact domain. -/
theorem partialMul_comm
    (P : SourceTopologicalPseudoMonoid.{u})
    (input : P.MultiplicationDomain) :
    P.partialMul input =
      P.partialMul
        ⟨(input.1.2, input.1.1), by simpa only [mul_comm] using input.2⟩ := by
  apply Subtype.ext
  exact mul_comm _ _

/-- Associativity holds whenever both parenthesized products are defined. -/
theorem partialMul_assoc
    (P : SourceTopologicalPseudoMonoid.{u})
    (first second third : P.Carrier)
    (firstSecond : first.1 * second.1 ∈ P.carrierSet)
    (secondThird : second.1 * third.1 ∈ P.carrierSet)
    (leftDefined :
      (P.partialMul ⟨(first, second), firstSecond⟩).1 * third.1 ∈
        P.carrierSet)
    (rightDefined :
      first.1 * (P.partialMul ⟨(second, third), secondThird⟩).1 ∈
        P.carrierSet) :
    P.partialMul
        ⟨(P.partialMul ⟨(first, second), firstSecond⟩, third), leftDefined⟩ =
      P.partialMul
        ⟨(first, P.partialMul ⟨(second, third), secondThird⟩), rightDefined⟩ := by
  apply Subtype.ext
  exact mul_assoc _ _ _

/-- The source definition of a divisible pseudo-monoid. -/
structure IsDivisible (P : SourceTopologicalPseudoMonoid.{u}) : Prop where
  ambient_roots :
    ∀ (n : ℕ+) (value : P.ambient),
      ∃ root : P.ambient, root ^ (n : ℕ) = value
  mem_power_iff :
    ∀ (n : ℕ+) (value : P.ambient),
      value ∈ P.carrierSet ↔ value ^ (n : ℕ) ∈ P.carrierSet

/-- The source definition of a cyclotomic pseudo-monoid. -/
structure IsCyclotomic (P : SourceTopologicalPseudoMonoid.{u}) : Prop where
  torsion_cyclotomic :
    Nonempty
      (CommGroup.torsion P.ambient ≃*
        Multiplicative (AddCircle (1 : ℚ)))
  torsion_mem :
    ∀ root : CommGroup.torsion P.ambient,
      (root : P.ambient) ∈ P.carrierSet
  torsion_mul_mem :
    ∀ (root : CommGroup.torsion P.ambient) (value : P.Carrier),
      (root : P.ambient) * value.1 ∈ P.carrierSet

/-- A continuous map preserving every product defined in the source. -/
structure Hom
    (source target : SourceTopologicalPseudoMonoid.{u}) where
  toFun : source.Carrier → target.Carrier
  continuous_toFun : Continuous toFun
  maps_domain :
    ∀ input : source.MultiplicationDomain,
      (toFun input.1.1).1 * (toFun input.1.2).1 ∈ target.carrierSet
  map_partialMul :
    ∀ input : source.MultiplicationDomain,
      toFun (source.partialMul input) =
        target.partialMul
          ⟨(toFun input.1.1, toFun input.1.2), maps_domain input⟩

namespace Hom

variable
  {first second third fourth : SourceTopologicalPseudoMonoid.{u}}

instance : CoeFun (Hom first second) fun _ => first.Carrier → second.Carrier :=
  ⟨Hom.toFun⟩

/-- A pseudo-monoid morphism is continuous on the embedded carriers. -/
theorem continuous (map : Hom first second) : Continuous map :=
  map.continuous_toFun

/-- Identity pseudo-monoid morphism. -/
def id (P : SourceTopologicalPseudoMonoid.{u}) : Hom P P where
  toFun := fun value => value
  continuous_toFun := continuous_id
  maps_domain input := input.2
  map_partialMul _ := rfl

/-- Composition of pseudo-monoid morphisms. -/
def comp
    (firstMap : Hom first second)
    (secondMap : Hom second third) : Hom first third where
  toFun := secondMap ∘ firstMap
  continuous_toFun := secondMap.continuous.comp firstMap.continuous
  maps_domain input :=
    secondMap.maps_domain
      ⟨(firstMap input.1.1, firstMap input.1.2), firstMap.maps_domain input⟩
  map_partialMul input := by
    change
      secondMap (firstMap (first.partialMul input)) =
        third.partialMul
          ⟨(secondMap (firstMap input.1.1), secondMap (firstMap input.1.2)), _⟩
    rw [firstMap.map_partialMul, secondMap.map_partialMul]

@[simp]
theorem comp_apply
    (firstMap : Hom first second)
    (secondMap : Hom second third)
    (value : first.Carrier) :
    firstMap.comp secondMap value = secondMap (firstMap value) := rfl

@[ext]
theorem ext
    (firstMap secondMap : Hom first second)
    (function_eq : ∀ value, firstMap value = secondMap value) :
    firstMap = secondMap := by
  cases firstMap with
  | mk firstFun firstContinuous firstDomain firstMul =>
      cases secondMap with
      | mk secondFun secondContinuous secondDomain secondMul =>
          have fun_eq : firstFun = secondFun := funext function_eq
          cases fun_eq
          rfl

theorem id_comp (map : Hom first second) : (id first).comp map = map := by
  apply ext
  intro value
  rfl

theorem comp_id (map : Hom first second) : map.comp (id second) = map := by
  apply ext
  intro value
  rfl

theorem comp_assoc
    (firstMap : Hom first second)
    (secondMap : Hom second third)
    (thirdMap : Hom third fourth) :
    (firstMap.comp secondMap).comp thirdMap =
      firstMap.comp (secondMap.comp thirdMap) := by
  apply ext
  intro value
  rfl

end Hom

instance : Category SourceTopologicalPseudoMonoid where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

namespace Iso

variable
  {first second third : SourceTopologicalPseudoMonoid.{u}}

/-- The carrier homeomorphism underlying an isomorphism of pseudo-monoids. -/
def toHomeomorph (iso : first ≅ second) : first.Carrier ≃ₜ second.Carrier where
  toFun := iso.hom.toFun
  invFun := iso.inv.toFun
  left_inv value := by
    have equality :=
      congrArg (fun map : first ⟶ first => map.toFun value) iso.hom_inv_id
    exact equality
  right_inv value := by
    have equality :=
      congrArg (fun map : second ⟶ second => map.toFun value) iso.inv_hom_id
    exact equality
  continuous_toFun := iso.hom.continuous
  continuous_invFun := iso.inv.continuous

/-- Isomorphisms reflect, as well as preserve, the domain of multiplication. -/
theorem maps_domain_iff
    (iso : first ≅ second)
    (firstValue secondValue : first.Carrier) :
    firstValue.1 * secondValue.1 ∈ first.carrierSet ↔
      (iso.hom.toFun firstValue).1 * (iso.hom.toFun secondValue).1 ∈
        second.carrierSet := by
  constructor
  · intro sourceDomain
    exact iso.hom.maps_domain ⟨(firstValue, secondValue), sourceDomain⟩
  · intro targetDomain
    have inverseDomain :=
      iso.inv.maps_domain
        ⟨(iso.hom.toFun firstValue, iso.hom.toFun secondValue), targetDomain⟩
    have first_inverse :
        iso.inv.toFun (iso.hom.toFun firstValue) = firstValue :=
      (toHomeomorph iso).symm_apply_apply firstValue
    have second_inverse :
        iso.inv.toFun (iso.hom.toFun secondValue) = secondValue :=
      (toHomeomorph iso).symm_apply_apply secondValue
    rw [first_inverse, second_inverse] at inverseDomain
    exact inverseDomain

end Iso

end SourceTopologicalPseudoMonoid

/-- A topological group acting continuously by pseudo-monoid automorphisms. -/
structure SourceTopologicalGroupPseudoMonoidActionPair where
  actingGroup : TopologicalGroupCat.{u}
  pseudoMonoid : SourceTopologicalPseudoMonoid.{u}
  action :
    actingGroup →*
      CategoryTheory.Aut pseudoMonoid
  continuous_action :
    Continuous fun input : actingGroup × pseudoMonoid.Carrier =>
      (action input.1).hom.toFun input.2

namespace SourceTopologicalGroupPseudoMonoidActionPair

/-- The identity of the acting group acts identically on the carrier. -/
theorem one_action
    (pair : SourceTopologicalGroupPseudoMonoidActionPair.{u})
    (value : pair.pseudoMonoid.Carrier) :
    (pair.action 1).hom.toFun value = value := by
  have equality := congrArg
    (fun automorphism : CategoryTheory.Aut pair.pseudoMonoid =>
      automorphism.hom.toFun value)
    pair.action.map_one
  exact equality

/-- Multiplication in the acting group gives composition of carrier actions. -/
theorem mul_action
    (pair : SourceTopologicalGroupPseudoMonoidActionPair.{u})
    (first second : pair.actingGroup)
    (value : pair.pseudoMonoid.Carrier) :
    (pair.action (first * second)).hom.toFun value =
      (pair.action first).hom.toFun ((pair.action second).hom.toFun value) := by
  have equality := congrArg
    (fun automorphism : CategoryTheory.Aut pair.pseudoMonoid =>
      automorphism.hom.toFun value)
    (pair.action.map_mul first second)
  exact equality

/-- Every group element preserves and reflects where multiplication is defined. -/
theorem action_maps_domain_iff
    (pair : SourceTopologicalGroupPseudoMonoidActionPair.{u})
    (groupElement : pair.actingGroup)
    (first second : pair.pseudoMonoid.Carrier) :
    first.1 * second.1 ∈ pair.pseudoMonoid.carrierSet ↔
      ((pair.action groupElement).hom.toFun first).1 *
          ((pair.action groupElement).hom.toFun second).1 ∈
        pair.pseudoMonoid.carrierSet :=
  SourceTopologicalPseudoMonoid.Iso.maps_domain_iff
    (pair.action groupElement) first second

/-- Every group element preserves the restricted pseudo-monoid product. -/
theorem action_partialMul
    (pair : SourceTopologicalGroupPseudoMonoidActionPair.{u})
    (groupElement : pair.actingGroup)
    (input : pair.pseudoMonoid.MultiplicationDomain) :
    (pair.action groupElement).hom.toFun
        (pair.pseudoMonoid.partialMul input) =
      pair.pseudoMonoid.partialMul
        ⟨((pair.action groupElement).hom.toFun input.1.1,
            (pair.action groupElement).hom.toFun input.1.2),
          (pair.action groupElement).hom.maps_domain input⟩ :=
  (pair.action groupElement).hom.map_partialMul input

/-- A carrier element fixed by every element of the acting group. -/
def IsFixed
    (pair : SourceTopologicalGroupPseudoMonoidActionPair.{u})
    (value : pair.pseudoMonoid.Carrier) : Prop :=
  ∀ groupElement,
    (pair.action groupElement).hom.toFun value = value

/--
The fixedness predicate on the ambient group.  Quantifying over the proof of
carrier membership makes the definition independent of subtype proof terms.
-/
def IsFixedAmbient
    (pair : SourceTopologicalGroupPseudoMonoidActionPair.{u})
    (value : pair.pseudoMonoid.ambient) : Prop :=
  ∀ (membership : value ∈ pair.pseudoMonoid.carrierSet) groupElement,
    (pair.action groupElement).hom.toFun ⟨value, membership⟩ =
      ⟨value, membership⟩

/-- The invariant sub-pseudo-monoid of a continuous action. -/
def fixedPseudoMonoid
    (pair : SourceTopologicalGroupPseudoMonoidActionPair.{u}) :
    SourceTopologicalPseudoMonoid.{u} where
  ambient := pair.pseudoMonoid.ambient
  carrierSet :=
    { value |
      value ∈ pair.pseudoMonoid.carrierSet ∧
        pair.IsFixedAmbient value }

namespace fixedPseudoMonoid

variable (pair : SourceTopologicalGroupPseudoMonoidActionPair.{u})

/-- A fixed carrier element, regarded as an element of the original carrier. -/
def toOriginal : pair.fixedPseudoMonoid.Carrier →
    pair.pseudoMonoid.Carrier :=
  fun value => ⟨value.1, value.2.1⟩

/-- The invariant carrier is exactly the subtype of fixed original elements. -/
def carrierEquiv :
    pair.fixedPseudoMonoid.Carrier ≃
      { value : pair.pseudoMonoid.Carrier // pair.IsFixed value } where
  toFun value :=
    ⟨⟨value.1, value.2.1⟩, fun groupElement =>
      value.2.2 value.2.1 groupElement⟩
  invFun value :=
    ⟨value.1.1,
      ⟨value.1.2, fun membership groupElement => by
        have fixed := value.2 groupElement
        simpa only [Subsingleton.elim membership value.1.2] using fixed⟩⟩
  left_inv value := by
    apply Subtype.ext
    rfl
  right_inv value := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Inclusion of the invariant sub-pseudo-monoid into the original one. -/
def inclusion : pair.fixedPseudoMonoid ⟶ pair.pseudoMonoid where
  toFun := fixedPseudoMonoid.toOriginal pair
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  maps_domain input := input.2.1
  map_partialMul _ := rfl

/-- The fixed-carrier inclusion is a topological embedding. -/
theorem inclusion_isEmbedding :
    Topology.IsEmbedding (fixedPseudoMonoid.inclusion pair).toFun := by
  let carrierSubset :
      pair.fixedPseudoMonoid.carrierSet ⊆
        pair.pseudoMonoid.carrierSet :=
    fun _ membership => membership.1
  simpa only [inclusion, toOriginal, Set.inclusion] using
    Topology.IsEmbedding.inclusion carrierSubset

/-- The fixed-carrier inclusion is injective. -/
theorem inclusion_injective :
    Function.Injective (fixedPseudoMonoid.inclusion pair).toFun :=
  (fixedPseudoMonoid.inclusion_isEmbedding pair).injective

/--
Products of fixed elements are fixed whenever the corresponding product is
defined in the original pseudo-monoid.  Thus passage to invariants introduces
no additional partial-multiplication obstruction.
-/
theorem mul_mem_iff
    (first second : (pair.fixedPseudoMonoid).Carrier) :
    first.1 * second.1 ∈ pair.fixedPseudoMonoid.carrierSet ↔
      first.1 * second.1 ∈ pair.pseudoMonoid.carrierSet := by
  constructor
  · exact fun membership => membership.1
  · intro productMembership
    refine ⟨productMembership, ?_⟩
    intro membership groupElement
    let firstOriginal : pair.pseudoMonoid.Carrier :=
      ⟨first.1, first.2.1⟩
    let secondOriginal : pair.pseudoMonoid.Carrier :=
      ⟨second.1, second.2.1⟩
    let input : pair.pseudoMonoid.MultiplicationDomain :=
      ⟨(firstOriginal, secondOriginal), productMembership⟩
    have firstFixed :
        (pair.action groupElement).hom.toFun firstOriginal =
          firstOriginal :=
      first.2.2 first.2.1 groupElement
    have secondFixed :
        (pair.action groupElement).hom.toFun secondOriginal =
          secondOriginal :=
      second.2.2 second.2.1 groupElement
    let actedInput : pair.pseudoMonoid.MultiplicationDomain :=
      ⟨((pair.action groupElement).hom.toFun firstOriginal,
          (pair.action groupElement).hom.toFun secondOriginal),
        (pair.action groupElement).hom.maps_domain input⟩
    have productFixed := pair.action_partialMul groupElement input
    have inputProduct :
        pair.pseudoMonoid.partialMul input =
          ⟨first.1 * second.1, membership⟩ := by
      apply Subtype.ext
      rfl
    have actedProduct :
        pair.pseudoMonoid.partialMul actedInput =
          ⟨first.1 * second.1, membership⟩ := by
      apply Subtype.ext
      change
        ((pair.action groupElement).hom.toFun firstOriginal).1 *
            ((pair.action groupElement).hom.toFun secondOriginal).1 =
          first.1 * second.1
      rw [firstFixed, secondFixed]
      rfl
    calc
      (pair.action groupElement).hom.toFun
          ⟨first.1 * second.1, membership⟩ =
        (pair.action groupElement).hom.toFun
          (pair.pseudoMonoid.partialMul input) :=
            congrArg (pair.action groupElement).hom.toFun
              inputProduct.symm
      _ = pair.pseudoMonoid.partialMul actedInput := productFixed
      _ = ⟨first.1 * second.1, membership⟩ := actedProduct

/-- The original product gives a product in the invariant pseudo-monoid. -/
def multiplicationDomainOfOriginal
    (first second : (pair.fixedPseudoMonoid).Carrier)
    (productMembership :
      first.1 * second.1 ∈ pair.pseudoMonoid.carrierSet) :
    pair.fixedPseudoMonoid.MultiplicationDomain :=
  ⟨(first, second),
    (fixedPseudoMonoid.mul_mem_iff pair first second).2
      productMembership⟩

end fixedPseudoMonoid

/-- An equivariant continuous morphism of topological action pairs. -/
structure Hom
    (source target : SourceTopologicalGroupPseudoMonoidActionPair.{u}) where
  groupHom : source.actingGroup ⟶ target.actingGroup
  pseudoMonoidHom : source.pseudoMonoid ⟶ target.pseudoMonoid
  equivariant :
    ∀ groupElement pseudoMonoidElement,
      pseudoMonoidHom.toFun
          ((source.action groupElement).hom.toFun pseudoMonoidElement) =
        (target.action (groupHom.toMonoidHom groupElement)).hom.toFun
          (pseudoMonoidHom.toFun pseudoMonoidElement)

namespace Hom

variable
  {first second third fourth :
    SourceTopologicalGroupPseudoMonoidActionPair.{u}}

/-- Identity equivariant morphism. -/
def id (pair : SourceTopologicalGroupPseudoMonoidActionPair.{u}) : Hom pair pair where
  groupHom := 𝟙 pair.actingGroup
  pseudoMonoidHom := 𝟙 pair.pseudoMonoid
  equivariant _ _ := rfl

/-- Composition of equivariant morphisms. -/
def comp (firstMap : Hom first second) (secondMap : Hom second third) :
    Hom first third where
  groupHom := firstMap.groupHom ≫ secondMap.groupHom
  pseudoMonoidHom := firstMap.pseudoMonoidHom ≫ secondMap.pseudoMonoidHom
  equivariant groupElement pseudoMonoidElement := by
    change
      secondMap.pseudoMonoidHom.toFun
          (firstMap.pseudoMonoidHom.toFun
            ((first.action groupElement).hom.toFun pseudoMonoidElement)) =
        (third.action
            (secondMap.groupHom.toMonoidHom
              (firstMap.groupHom.toMonoidHom groupElement))).hom.toFun
          (secondMap.pseudoMonoidHom.toFun
            (firstMap.pseudoMonoidHom.toFun pseudoMonoidElement))
    rw [firstMap.equivariant, secondMap.equivariant]

@[ext]
theorem ext
    (firstMap secondMap : Hom first second)
    (groupHom_eq : firstMap.groupHom = secondMap.groupHom)
    (pseudoMonoidHom_eq :
      firstMap.pseudoMonoidHom = secondMap.pseudoMonoidHom) :
    firstMap = secondMap := by
  cases firstMap
  cases secondMap
  cases groupHom_eq
  cases pseudoMonoidHom_eq
  rfl

theorem id_comp (map : Hom first second) : (id first).comp map = map := by
  apply ext
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  · apply SourceTopologicalPseudoMonoid.Hom.ext
    intro value
    rfl

theorem comp_id (map : Hom first second) : map.comp (id second) = map := by
  apply ext
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  · apply SourceTopologicalPseudoMonoid.Hom.ext
    intro value
    rfl

theorem comp_assoc
    (firstMap : Hom first second)
    (secondMap : Hom second third)
    (thirdMap : Hom third fourth) :
    (firstMap.comp secondMap).comp thirdMap =
      firstMap.comp (secondMap.comp thirdMap) := by
  apply ext
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  · apply SourceTopologicalPseudoMonoid.Hom.ext
    intro value
    rfl

end Hom

instance : Category SourceTopologicalGroupPseudoMonoidActionPair where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

/-- An isomorphism of topological group/pseudo-monoid action pairs. -/
structure Iso
    (source target : SourceTopologicalGroupPseudoMonoidActionPair.{u}) where
  groupIso : source.actingGroup ≃ₜ* target.actingGroup
  pseudoMonoidIso : source.pseudoMonoid ≅ target.pseudoMonoid
  equivariant :
    ∀ groupElement pseudoMonoidElement,
      pseudoMonoidIso.hom.toFun
          ((source.action groupElement).hom.toFun pseudoMonoidElement) =
        (target.action (groupIso groupElement)).hom.toFun
          (pseudoMonoidIso.hom.toFun pseudoMonoidElement)

namespace Iso

variable
  {first second third :
    SourceTopologicalGroupPseudoMonoidActionPair.{u}}

/-- Identity isomorphism of an action pair. -/
def refl (pair : SourceTopologicalGroupPseudoMonoidActionPair.{u}) :
    Iso pair pair where
  groupIso := _root_.ContinuousMulEquiv.refl pair.actingGroup
  pseudoMonoidIso := CategoryTheory.Iso.refl pair.pseudoMonoid
  equivariant _ _ := rfl

/-- Composition of action-pair isomorphisms. -/
def trans
    (firstIso : Iso first second)
    (secondIso : Iso second third) : Iso first third where
  groupIso := firstIso.groupIso.trans secondIso.groupIso
  pseudoMonoidIso := firstIso.pseudoMonoidIso.trans secondIso.pseudoMonoidIso
  equivariant groupElement pseudoMonoidElement := by
    change
      secondIso.pseudoMonoidIso.hom.toFun
          (firstIso.pseudoMonoidIso.hom.toFun
            ((first.action groupElement).hom.toFun pseudoMonoidElement)) =
        (third.action
            (secondIso.groupIso (firstIso.groupIso groupElement))).hom.toFun
          (secondIso.pseudoMonoidIso.hom.toFun
            (firstIso.pseudoMonoidIso.hom.toFun pseudoMonoidElement))
    rw [firstIso.equivariant, secondIso.equivariant]

/-- Inverse of an action-pair isomorphism. -/
def symm (pairIso : Iso first second) : Iso second first where
  groupIso := pairIso.groupIso.symm
  pseudoMonoidIso := pairIso.pseudoMonoidIso.symm
  equivariant groupElement pseudoMonoidElement := by
    apply (SourceTopologicalPseudoMonoid.Iso.toHomeomorph
      pairIso.pseudoMonoidIso).injective
    change
      pairIso.pseudoMonoidIso.hom.toFun
          (pairIso.pseudoMonoidIso.inv.toFun
            ((second.action groupElement).hom.toFun pseudoMonoidElement)) =
        pairIso.pseudoMonoidIso.hom.toFun
          ((first.action (pairIso.groupIso.symm groupElement)).hom.toFun
            (pairIso.pseudoMonoidIso.inv.toFun pseudoMonoidElement))
    rw [pairIso.equivariant]
    have action_cancel :
        pairIso.pseudoMonoidIso.hom.toFun
            (pairIso.pseudoMonoidIso.inv.toFun
              ((second.action groupElement).hom.toFun pseudoMonoidElement)) =
          (second.action groupElement).hom.toFun pseudoMonoidElement :=
      (SourceTopologicalPseudoMonoid.Iso.toHomeomorph
        pairIso.pseudoMonoidIso).apply_symm_apply _
    have value_cancel :
        pairIso.pseudoMonoidIso.hom.toFun
            (pairIso.pseudoMonoidIso.inv.toFun pseudoMonoidElement) =
          pseudoMonoidElement :=
      (SourceTopologicalPseudoMonoid.Iso.toHomeomorph
        pairIso.pseudoMonoidIso).apply_symm_apply _
    rw [action_cancel, value_cancel, pairIso.groupIso.apply_symm_apply]

/-- The forward equivariant morphism of an action-pair isomorphism. -/
def hom (pairIso : Iso first second) : first ⟶ second where
  groupHom :=
    { toMonoidHom := pairIso.groupIso.toMulEquiv.toMonoidHom
      continuous_toFun := pairIso.groupIso.continuous_toFun }
  pseudoMonoidHom := pairIso.pseudoMonoidIso.hom
  equivariant := pairIso.equivariant

@[simp]
theorem refl_hom
    (pair : SourceTopologicalGroupPseudoMonoidActionPair.{u}) :
    (refl pair).hom = 𝟙 pair := by
  apply Hom.ext
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  · apply SourceTopologicalPseudoMonoid.Hom.ext
    intro value
    rfl

@[simp]
theorem trans_hom
    (firstIso : Iso first second)
    (secondIso : Iso second third) :
    (firstIso.trans secondIso).hom = firstIso.hom ≫ secondIso.hom := by
  apply Hom.ext
  · apply _root_.ContinuousMonoidHom.ext
    intro
    rfl
  · apply SourceTopologicalPseudoMonoid.Hom.ext
    intro value
    rfl

/-- An action-pair isomorphism as an isomorphism in the action-pair category. -/
def toCategoryIso (pairIso : Iso first second) : first ≅ second where
  hom := pairIso.hom
  inv := pairIso.symm.hom
  hom_inv_id := by
    apply Hom.ext
    · apply _root_.ContinuousMonoidHom.ext
      intro value
      exact pairIso.groupIso.symm_apply_apply value
    · apply SourceTopologicalPseudoMonoid.Hom.ext
      intro value
      exact congrArg
        (fun map : first.pseudoMonoid ⟶ first.pseudoMonoid => map.toFun value)
        pairIso.pseudoMonoidIso.hom_inv_id
  inv_hom_id := by
    apply Hom.ext
    · apply _root_.ContinuousMonoidHom.ext
      intro value
      exact pairIso.groupIso.apply_symm_apply value
    · apply SourceTopologicalPseudoMonoid.Hom.ext
      intro value
      exact congrArg
        (fun map : second.pseudoMonoid ⟶ second.pseudoMonoid => map.toFun value)
        pairIso.pseudoMonoidIso.inv_hom_id

end Iso

end SourceTopologicalGroupPseudoMonoidActionPair

/-! ## Profinite quotient descent -/

/--
A continuous profinite-group action on a topological pseudo-monoid.  This is
the specialized action pair used by the nonarchimedean clauses of IUT I,
Definition 5.2(v)-(vi).
-/
structure SourceProfinitePseudoMonoidActionPair
    (group : ProfiniteGrp.{u}) where
  pseudoMonoid : SourceTopologicalPseudoMonoid.{u}
  action : group →* CategoryTheory.Aut pseudoMonoid
  continuous_action :
    Continuous fun input : group × pseudoMonoid.Carrier =>
      (action input.1).hom.toFun input.2

namespace SourceProfinitePseudoMonoidActionPair

variable {source quotient : ProfiniteGrp.{u}}

@[ext]
theorem ext
    (first second : SourceProfinitePseudoMonoidActionPair source)
    (pseudoMonoid_eq : first.pseudoMonoid = second.pseudoMonoid)
    (action_eq : HEq first.action second.action) :
    first = second := by
  cases first with
  | mk firstPseudoMonoid firstAction firstContinuous =>
      cases second with
      | mk secondPseudoMonoid secondAction secondContinuous =>
          cases pseudoMonoid_eq
          have actionEquality : firstAction = secondAction :=
            eq_of_heq action_eq
          cases actionEquality
          rfl

/-- Regard a profinite action as a general topological-group action pair. -/
def toTopologicalActionPair
    (pair : SourceProfinitePseudoMonoidActionPair source) :
    SourceTopologicalGroupPseudoMonoidActionPair.{u} where
  actingGroup := TopologicalGroupCat.ofProfinite source
  pseudoMonoid := pair.pseudoMonoid
  action := pair.action
  continuous_action := pair.continuous_action

/-- Pull a profinite action back along a continuous group homomorphism. -/
def comap
    (pair : SourceProfinitePseudoMonoidActionPair quotient)
    (map : source ⟶ quotient) :
    SourceProfinitePseudoMonoidActionPair source where
  pseudoMonoid := pair.pseudoMonoid
  action := pair.action.comp map.hom.toMonoidHom
  continuous_action :=
    pair.continuous_action.comp
      ((map.hom.continuous_toFun.comp continuous_fst).prodMk
        continuous_snd)

@[simp]
theorem comap_action
    (pair : SourceProfinitePseudoMonoidActionPair quotient)
    (map : source ⟶ quotient)
    (groupElement : source) :
    (pair.comap map).action groupElement = pair.action (map groupElement) :=
  rfl

/-- The exact algebraic condition for an action to descend through a quotient. -/
def KernelActsTrivially
    (pair : SourceProfinitePseudoMonoidActionPair source)
    (map : source ⟶ quotient) : Prop :=
  map.hom.toMonoidHom.ker ≤ pair.action.ker

/-- Construct the quotient action algebraically from kernel triviality. -/
noncomputable def quotientAction
    (pair : SourceProfinitePseudoMonoidActionPair source)
    (map : source ⟶ quotient)
    (map_surjective : Function.Surjective map)
    (kernel_trivial : pair.KernelActsTrivially map) :
    quotient →* CategoryTheory.Aut pair.pseudoMonoid :=
  map.hom.toMonoidHom.liftOfSurjective map_surjective
    ⟨pair.action, kernel_trivial⟩

/-- The descended action pulls back to the original action. -/
theorem quotientAction_comp
    (pair : SourceProfinitePseudoMonoidActionPair source)
    (map : source ⟶ quotient)
    (map_surjective : Function.Surjective map)
    (kernel_trivial : pair.KernelActsTrivially map) :
    (pair.quotientAction map map_surjective kernel_trivial).comp
        map.hom.toMonoidHom = pair.action := by
  simpa only [quotientAction] using
    map.hom.toMonoidHom.liftOfRightInverse_comp
      (Function.surjInv map_surjective)
      (Function.rightInverse_surjInv map_surjective)
      ⟨pair.action, kernel_trivial⟩

@[simp]
theorem quotientAction_map
    (pair : SourceProfinitePseudoMonoidActionPair source)
    (map : source ⟶ quotient)
    (map_surjective : Function.Surjective map)
    (kernel_trivial : pair.KernelActsTrivially map)
    (groupElement : source) :
    pair.quotientAction map map_surjective kernel_trivial
        (map groupElement) =
      pair.action groupElement := by
  have equality := congrArg
    (fun action : source →* CategoryTheory.Aut pair.pseudoMonoid =>
      action groupElement)
    (pair.quotientAction_comp map map_surjective kernel_trivial)
  exact equality

/--
Descent through a surjective morphism of profinite groups preserves continuity.
The proof uses compact-to-Hausdorff quotient topology and openness of quotient
homomorphisms, rather than assuming continuity of the descended action.
-/
noncomputable def descend
    (pair : SourceProfinitePseudoMonoidActionPair source)
    (map : source ⟶ quotient)
    (map_surjective : Function.Surjective map)
    (kernel_trivial : pair.KernelActsTrivially map) :
    SourceProfinitePseudoMonoidActionPair quotient where
  pseudoMonoid := pair.pseudoMonoid
  action := pair.quotientAction map map_surjective kernel_trivial
  continuous_action := by
    have quotientMap : Topology.IsQuotientMap map :=
      IsQuotientMap.of_surjective_continuous
        map_surjective map.hom.continuous_toFun
    have openQuotientMap : IsOpenQuotientMap map :=
      MonoidHom.isOpenQuotientMap_of_isQuotientMap quotientMap
    have productQuotientMap :
        IsOpenQuotientMap
          (Prod.map map
            (id : pair.pseudoMonoid.Carrier →
              pair.pseudoMonoid.Carrier)) :=
      openQuotientMap.prodMap IsOpenQuotientMap.id
    rw [productQuotientMap.isQuotientMap.continuous_iff]
    convert pair.continuous_action using 1
    ext input
    change
      ((pair.quotientAction map map_surjective kernel_trivial
          (map input.1)).hom.toFun input.2).1 =
        ((pair.action input.1).hom.toFun input.2).1
    rw [pair.quotientAction_map map map_surjective
      kernel_trivial input.1]

/-- Descending and then pulling back recovers the original action pair. -/
theorem comap_descend
    (pair : SourceProfinitePseudoMonoidActionPair source)
    (map : source ⟶ quotient)
    (map_surjective : Function.Surjective map)
    (kernel_trivial : pair.KernelActsTrivially map) :
    (pair.descend map map_surjective kernel_trivial).comap map = pair := by
  apply ext
  · rfl
  · exact heq_of_eq
      (pair.quotientAction_comp map map_surjective kernel_trivial)

/-- Any action pulled back from a quotient is trivial on the quotient kernel. -/
theorem comap_kernelActsTrivially
    (pair : SourceProfinitePseudoMonoidActionPair quotient)
    (map : source ⟶ quotient) :
    (pair.comap map).KernelActsTrivially map := by
  intro groupElement membership
  change pair.action (map groupElement) = 1
  change map groupElement = 1 at membership
  calc
    pair.action (map groupElement) = pair.action 1 :=
      congrArg pair.action membership
    _ = 1 := pair.action.map_one

end SourceProfinitePseudoMonoidActionPair

end Iut
