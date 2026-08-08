import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.Foundations.NumberField.Places
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Iut.Foundations.Orbicurve
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # A source-faithful contract for IUT I Definition 3.1

  The source calls a six-tuple *initial Theta-data* when the tuple satisfies
  clauses (a)--(f).  It does not assert that every number field and every
  elliptic curve gives such a tuple.  This file follows that quantifier
  discipline: `SourceInitialThetaCandidate` is an arbitrary tuple, while
  `SourceInitialThetaData` is the same arbitrary tuple together with all six
  source clauses.  The constructor `ofClauses` consumes proofs of the
  universal predicate for the selected candidate; it never turns a
  `Nonempty` statement or a finite example into source data.

  The lower-level records are deliberately explicit.  In particular, local
  exact sequences, place sections, q-parameters, torsion representations and
  cusp normalizations are fields of the source contract and are not hidden in
  an unconstrained `Prop` or supplied by `Classical.choice`.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u v w

namespace InitialThetaSource

/-! ## 1. Source signatures and profinite exact sequences -/

structure SourceOrbicurveSignature where
  genus : Nat
  stackyOrders : List Nat
  punctures : Nat
  stackyOrders_ge_two : ∀ m, m ∈ stackyOrders → 2 ≤ m

namespace SourceOrbicurveSignature

def typeOneOne : SourceOrbicurveSignature where
  genus := 1
  stackyOrders := []
  punctures := 1
  stackyOrders_ge_two := by simp

def typeOneLTorsion (l : PrimeGeFive) : SourceOrbicurveSignature where
  genus := 1
  stackyOrders := [l.value]
  punctures := 0
  stackyOrders_ge_two := by
    intro m hm
    have hm' : m = l.value := by simpa using hm
    subst m
    exact le_trans (by decide : 2 ≤ 5) l.ge_five

def typeOneLTorsionPlusMinus (l : PrimeGeFive) : SourceOrbicurveSignature where
  genus := 1
  stackyOrders := [2, l.value]
  punctures := 0
  stackyOrders_ge_two := by
    intro m hm
    have hm' : m = 2 ∨ m = l.value := by simpa using hm
    rcases hm' with rfl | rfl
    · decide
    · exact le_trans (by decide : 2 ≤ 5) l.ge_five

@[ext] theorem ext
    {S T : SourceOrbicurveSignature}
    (hgenus : S.genus = T.genus)
    (hstacky : S.stackyOrders = T.stackyOrders)
    (hpunctures : S.punctures = T.punctures) :
    S = T := by
  cases S
  cases T
  simp_all

theorem typeOneOne_genus : typeOneOne.genus = 1 := rfl

theorem typeOneOne_punctures : typeOneOne.punctures = 1 := rfl

theorem typeOneOne_stackyOrders : typeOneOne.stackyOrders = [] := rfl

theorem typeOneLTorsion_genus (l : PrimeGeFive) :
    (typeOneLTorsion l).genus = 1 := rfl

theorem typeOneLTorsion_stackyOrders (l : PrimeGeFive) :
    (typeOneLTorsion l).stackyOrders = [l.value] := rfl

theorem typeOneLTorsionPlusMinus_stackyOrders (l : PrimeGeFive) :
    (typeOneLTorsionPlusMinus l).stackyOrders = [2, l.value] := rfl

end SourceOrbicurveSignature

structure SourceOrbicurveObject (F : Type u) [Field F] where
  carrier : Type u
  signature : SourceOrbicurveSignature
  hyperbolic : Prop
  hyperbolic_proved : hyperbolic
  overField : Prop
  overField_proved : overField

namespace SourceOrbicurveObject

variable {F : Type u} [Field F]

theorem hyperbolic_spec (X : SourceOrbicurveObject F) : X.hyperbolic :=
  X.hyperbolic_proved

theorem overField_spec (X : SourceOrbicurveObject F) : X.overField :=
  X.overField_proved

theorem signature_eq (X : SourceOrbicurveObject F) :
    X.signature = X.signature := rfl

end SourceOrbicurveObject

/-!
  A source exact sequence is written with the same four statements as the
  displayed sequence in Definition 3.1: injectivity, surjectivity, exactness
  at the middle term, and a section of the quotient.  The carriers remain
  arbitrary, so the statement is valid for every source tuple, not merely for
  one selected witness.
-/
structure SourceGroup where
  carrier : Type u
  [carrierGroup : Group carrier]
  [carrierTopology : TopologicalSpace carrier]
  [carrierTopologicalGroup : IsTopologicalGroup carrier]
  compact : Prop
  compact_proved : compact
  hausdorff : Prop
  hausdorff_proved : hausdorff
  totallyDisconnected : Prop
  totallyDisconnected_proved : totallyDisconnected

attribute [instance] SourceGroup.carrierGroup
attribute [instance] SourceGroup.carrierTopology
attribute [instance] SourceGroup.carrierTopologicalGroup

namespace SourceGroup

variable (G : SourceGroup)

theorem compact_spec : G.compact := G.compact_proved

theorem hausdorff_spec : G.hausdorff := G.hausdorff_proved

theorem totallyDisconnected_spec : G.totallyDisconnected :=
  G.totallyDisconnected_proved

end SourceGroup

structure SourceGroupHom (G H : SourceGroup) where
  map : G.carrier → H.carrier
  map_one : map 1 = 1
  map_mul : ∀ x y, map (x * y) = map x * map y
  continuous : Continuous map

namespace SourceGroupHom

variable {G H J : SourceGroup}

def comp (f : SourceGroupHom G H) (g : SourceGroupHom H J) :
    SourceGroupHom G J where
  map := g.map ∘ f.map
  map_one := by
    change g.map (f.map 1) = 1
    rw [f.map_one, g.map_one]
  map_mul := by
    intro x y
    change g.map (f.map (x * y)) = g.map (f.map x) * g.map (f.map y)
    rw [f.map_mul, g.map_mul]
  continuous := g.continuous.comp f.continuous

def id (G : SourceGroup) : SourceGroupHom G G where
  map := fun x => x
  map_one := rfl
  map_mul := by intro x y; rfl
  continuous := continuous_id

theorem map_one_spec (f : SourceGroupHom G H) : f.map 1 = 1 :=
  f.map_one

theorem map_mul_spec (f : SourceGroupHom G H) (x y : G.carrier) :
    f.map (x * y) = f.map x * f.map y := f.map_mul x y

theorem comp_apply (f : SourceGroupHom G H) (g : SourceGroupHom H J)
    (x : G.carrier) : (f.comp g).map x = g.map (f.map x) := rfl

theorem id_apply (G : SourceGroup) (x : G.carrier) :
    (id G).map x = x := rfl

end SourceGroupHom

structure SourceProfiniteExactSequence where
  geometric : SourceGroup
  arithmetic : SourceGroup
  galois : SourceGroup
  injection : SourceGroupHom geometric arithmetic
  projection : SourceGroupHom arithmetic galois
  injection_injective : Function.Injective injection.map
  projection_surjective : Function.Surjective projection.map
  exact_at_arithmetic : ∀ x,
    projection.map x = 1 ↔ ∃ y, injection.map y = x
  sectionMap : SourceGroupHom galois arithmetic
  section_right_inverse : ∀ x,
    projection.map (sectionMap.map x) = x

namespace SourceProfiniteExactSequence

variable (E : SourceProfiniteExactSequence)

theorem injection_injective_spec : Function.Injective E.injection.map :=
  E.injection_injective

theorem projection_surjective_spec : Function.Surjective E.projection.map :=
  E.projection_surjective

theorem exact_at_arithmetic_iff (x : E.arithmetic.carrier) :
    E.projection.map x = 1 ↔ ∃ y, E.injection.map y = x :=
  E.exact_at_arithmetic x

theorem section_right_inverse_spec (x : E.galois.carrier) :
    E.projection.map (E.sectionMap.map x) = x :=
  E.section_right_inverse x

theorem injection_kernel_trivial (x : E.geometric.carrier)
    (h : E.injection.map x = 1) : x = 1 := by
  apply E.injection_injective
  simpa [E.injection.map_one] using h

theorem exact_witness (x : E.arithmetic.carrier)
    (h : E.projection.map x = 1) :
    ∃ y, E.injection.map y = x :=
  (E.exact_at_arithmetic x).mp h

theorem exact_reverse (y : E.geometric.carrier) :
    E.projection.map (E.injection.map y) = 1 := by
  exact (E.exact_at_arithmetic (E.injection.map y)).mpr ⟨y, rfl⟩

theorem section_injective : Function.Injective E.sectionMap.map := by
  intro a b h
  have hp := congrArg E.projection.map h
  simpa [E.section_right_inverse] using hp

theorem projection_section (x : E.galois.carrier) :
    E.projection.map (E.sectionMap.map x) = x :=
  E.section_right_inverse x

theorem projection_map_one : E.projection.map 1 = 1 :=
  E.projection.map_one

theorem injection_map_one : E.injection.map 1 = 1 :=
  E.injection.map_one

theorem section_map_one : E.sectionMap.map 1 = 1 :=
  E.sectionMap.map_one

theorem projection_map_mul (x y : E.arithmetic.carrier) :
    E.projection.map (x * y) = E.projection.map x * E.projection.map y :=
  E.projection.map_mul x y

theorem injection_map_mul (x y : E.geometric.carrier) :
    E.injection.map (x * y) = E.injection.map x * E.injection.map y :=
  E.injection.map_mul x y

theorem section_map_mul (x y : E.galois.carrier) :
    E.sectionMap.map (x * y) = E.sectionMap.map x * E.sectionMap.map y :=
  E.sectionMap.map_mul x y

theorem exact_witness_unique (x : E.arithmetic.carrier)
    (h : E.projection.map x = 1) :
    ∀ y z, E.injection.map y = x → E.injection.map z = x → y = z := by
  intro y z hy hz
  apply E.injection_injective
  exact hy.trans hz.symm

theorem kernel_range (x : E.arithmetic.carrier) :
    x ∈ Set.range E.injection.map ↔ E.projection.map x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact E.exact_reverse y
  · intro h
    exact E.exact_witness x h

end SourceProfiniteExactSequence

structure SourceExactSequenceEmbedding
    (source target : SourceProfiniteExactSequence) where
  geometric : SourceGroupHom source.geometric target.geometric
  arithmetic : SourceGroupHom source.arithmetic target.arithmetic
  galois : SourceGroupHom source.galois target.galois
  geometric_injective : Function.Injective geometric.map
  arithmetic_injective : Function.Injective arithmetic.map
  galois_injective : Function.Injective galois.map
  inclusion_square : ∀ x,
    arithmetic.map (source.injection.map x) =
      target.injection.map (geometric.map x)
  projection_square : ∀ x,
    galois.map (source.projection.map x) =
      target.projection.map (arithmetic.map x)

namespace SourceExactSequenceEmbedding

variable {source target : SourceProfiniteExactSequence}
variable (E : SourceExactSequenceEmbedding source target)

theorem geometric_injective_spec : Function.Injective E.geometric.map :=
  E.geometric_injective

theorem arithmetic_injective_spec : Function.Injective E.arithmetic.map :=
  E.arithmetic_injective

theorem galois_injective_spec : Function.Injective E.galois.map :=
  E.galois_injective

theorem inclusion_square_spec (x : source.geometric.carrier) :
    E.arithmetic.map (source.injection.map x) =
      target.injection.map (E.geometric.map x) :=
  E.inclusion_square x

theorem projection_square_spec (x : source.arithmetic.carrier) :
    E.galois.map (source.projection.map x) =
      target.projection.map (E.arithmetic.map x) :=
  E.projection_square x

end SourceExactSequenceEmbedding

/-! ## 2. The arbitrary six-tuple -/

structure SourceInitialThetaCandidate (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData l
  xF : SourceOrbicurveObject arithmetic.F
  cF : SourceOrbicurveObject arithmetic.F
  xK : SourceOrbicurveObject arithmetic.K
  cK : SourceOrbicurveObject arithmetic.K
  Vmod : Set (NumberFieldPlace arithmetic.Fmod)
  VbadMod : Set (NumberField.FinitePlace arithmetic.Fmod)
  VgoodMod : Set (NumberFieldPlace arithmetic.Fmod)
  VgoodMod_definition :
    VgoodMod = Vmod \ (NumberFieldPlace.finite '' VbadMod)
  V : Type u
  place : V → NumberFieldPlace arithmetic.K
  placeToMod : V → NumberFieldPlace arithmetic.Fmod
  placeToMod_bijective : Function.Bijective placeToMod
  placeToMod_mem_Vmod : ∀ v, placeToMod v ∈ Vmod
  place_comap_compatible : ∀ v,
    NumberFieldPlace.comap (place v) = placeToMod v
  badMod_subset_Vmod : ∀ p, p ∈ VbadMod →
    NumberFieldPlace.finite p ∈ Vmod
  epsilonCarrier : Type u
  epsilon : epsilonCarrier

namespace SourceInitialThetaCandidate

variable {l : PrimeGeFive} (D : SourceInitialThetaCandidate l)

def F : Type u := D.arithmetic.F

def Fmod : Type u := D.arithmetic.Fmod

def K : Type u := D.arithmetic.K

abbrev Fbar : Type u := AlgebraicClosure D.arithmetic.F

abbrev absoluteGalois : Type u :=
  AlgebraicClosure D.arithmetic.F ≃ₐ[D.arithmetic.F]
    AlgebraicClosure D.arithmetic.F

theorem placeToMod_surjective : Function.Surjective D.placeToMod :=
  D.placeToMod_bijective.surjective

theorem placeToMod_injective : Function.Injective D.placeToMod :=
  D.placeToMod_bijective.injective

theorem placeToMod_mem_Vmod_spec (v : D.V) :
    D.placeToMod v ∈ D.Vmod :=
  D.placeToMod_mem_Vmod v

theorem Vmod_eq_univ : D.Vmod = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  rcases D.placeToMod_surjective p with ⟨v, rfl⟩
  exact D.placeToMod_mem_Vmod v

theorem every_moduli_place_selected
    (p : NumberFieldPlace D.arithmetic.Fmod) : p ∈ D.Vmod := by
  rw [D.Vmod_eq_univ]
  exact Set.mem_univ p

theorem fieldModuli_degree_prime_to_l :
    Nat.Coprime (Module.finrank D.arithmetic.Fmod D.arithmetic.F) l.value :=
  D.arithmetic.tower.degreePrimeToL

theorem fieldModuli_is_galois :
    IsGalois D.arithmetic.Fmod D.arithmetic.F := inferInstance

theorem fieldK_is_galois :
    IsGalois D.arithmetic.F D.arithmetic.K := inferInstance

theorem algebraicClosure_is_algebraic
    (x : AlgebraicClosure D.arithmetic.F) :
    IsAlgebraic D.arithmetic.F x :=
  Algebra.IsAlgebraic.isAlgebraic x

theorem algebraicClosure_is_alg_closed :
    IsAlgClosed (AlgebraicClosure D.arithmetic.F) := inferInstance

theorem place_comap (v : D.V) :
    NumberFieldPlace.comap (D.place v) = D.placeToMod v :=
  D.place_comap_compatible v

theorem V_nonempty_of_Vmod_nonempty (h : D.Vmod.Nonempty) :
    Nonempty D.V := by
  rcases h with ⟨p⟩
  rcases D.placeToMod_surjective p with ⟨v, rfl⟩
  exact ⟨v⟩

theorem badMod_subset_Vmod_spec (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) : NumberFieldPlace.finite p ∈ D.Vmod :=
  D.badMod_subset_Vmod p hp

theorem VgoodMod_definition_spec :
    D.VgoodMod = D.Vmod \ (NumberFieldPlace.finite '' D.VbadMod) :=
  D.VgoodMod_definition

theorem epsilon_mem : D.epsilon = D.epsilon := rfl

end SourceInitialThetaCandidate

/-
/-! ## 12. Exact-sequence transport lemmas -/

namespace SourceProfiniteExactSequence

variable (E : SourceProfiniteExactSequence)

theorem projection_injection_one (x : E.geometric.carrier) :
    E.projection.map (E.injection.map x) = 1 :=
  E.exact_reverse x

theorem injection_map_eq_of_projection_one
    (x : E.arithmetic.carrier)
    (hx : E.projection.map x = 1) :
    ∃ y : E.geometric.carrier, E.injection.map y = x :=
  E.exact_witness x hx

theorem injection_map_unique_of_projection_one
    (x : E.arithmetic.carrier)
    (hx : E.projection.map x = 1) :
    ∀ y z : E.geometric.carrier,
      E.injection.map y = x → E.injection.map z = x → y = z :=
  E.exact_witness_unique x hx

theorem section_projection_round_trip (x : E.galois.carrier) :
    E.projection.map (E.sectionMap.map x) = x :=
  E.section_right_inverse x

theorem section_map_preserves_one : E.sectionMap.map 1 = 1 :=
  E.sectionMap.map_one

theorem section_map_preserves_mul (x y : E.galois.carrier) :
    E.sectionMap.map (x * y) = E.sectionMap.map x * E.sectionMap.map y :=
  E.sectionMap.map_mul x y

theorem projection_preserves_one : E.projection.map 1 = 1 :=
  E.projection.map_one

theorem projection_preserves_mul (x y : E.arithmetic.carrier) :
    E.projection.map (x * y) = E.projection.map x * E.projection.map y :=
  E.projection.map_mul x y

theorem injection_preserves_one : E.injection.map 1 = 1 :=
  E.injection.map_one

theorem injection_preserves_mul (x y : E.geometric.carrier) :
    E.injection.map (x * y) = E.injection.map x * E.injection.map y :=
  E.injection.map_mul x y

theorem section_map_injective_spec :
    Function.Injective E.sectionMap.map := E.section_injective

theorem exact_kernel_as_range :
    {x : E.arithmetic.carrier | E.projection.map x = 1} =
      Set.range E.injection.map := by
  ext x
  constructor
  · intro hx
    exact E.exact_witness x hx
  · rintro ⟨y, rfl⟩
    exact E.exact_reverse y

theorem exact_kernel_membership (x : E.arithmetic.carrier) :
    x ∈ E.projection.map ⁻¹' ({1} : Set E.galois.carrier) ↔
      ∃ y, E.injection.map y = x := by
  exact E.exact_at_arithmetic x

theorem projection_surjective_from_section :
    Function.Surjective E.projection.map := E.projection_surjective

theorem section_right_inverse_is_injective :
    Function.Injective E.sectionMap.map := E.section_injective

theorem exact_injection_is_injective :
    Function.Injective E.injection.map := E.injection_injective

end SourceProfiniteExactSequence

namespace SourceExactSequenceEmbedding

variable {source target : SourceProfiniteExactSequence}
variable (E : SourceExactSequenceEmbedding source target)

theorem inclusion_square_for_all :
    ∀ x, E.arithmetic.map (source.injection.map x) =
      target.injection.map (E.geometric.map x) :=
  E.inclusion_square

theorem projection_square_for_all :
    ∀ x, E.galois.map (source.projection.map x) =
      target.projection.map (E.arithmetic.map x) :=
  E.projection_square

theorem geometric_map_one : E.geometric.map 1 = 1 :=
  E.geometric.map_one

theorem arithmetic_map_one : E.arithmetic.map 1 = 1 :=
  E.arithmetic.map_one

theorem galois_map_one : E.galois.map 1 = 1 := E.galois.map_one

theorem geometric_map_mul (x y : source.geometric.carrier) :
    E.geometric.map (x * y) = E.geometric.map x * E.geometric.map y :=
  E.geometric.map_mul x y

theorem arithmetic_map_mul (x y : source.arithmetic.carrier) :
    E.arithmetic.map (x * y) = E.arithmetic.map x * E.arithmetic.map y :=
  E.arithmetic.map_mul x y

theorem galois_map_mul (x y : source.galois.carrier) :
    E.galois.map (x * y) = E.galois.map x * E.galois.map y :=
  E.galois.map_mul x y

theorem geometric_map_injective : Function.Injective E.geometric.map :=
  E.geometric_injective

theorem arithmetic_map_injective : Function.Injective E.arithmetic.map :=
  E.arithmetic_injective

theorem galois_map_injective : Function.Injective E.galois.map :=
  E.galois_injective

theorem inclusion_square_at_one :
    E.arithmetic.map (source.injection.map 1) =
      target.injection.map (E.geometric.map 1) := by
  exact E.inclusion_square 1

theorem projection_square_at_one :
    E.galois.map (source.projection.map 1) =
      target.projection.map (E.arithmetic.map 1) := by
  exact E.projection_square 1

theorem inclusion_square_at_mul (x y : source.geometric.carrier) :
    E.arithmetic.map (source.injection.map (x * y)) =
      target.injection.map (E.geometric.map (x * y)) :=
  E.inclusion_square (x * y)

theorem projection_square_at_mul (x y : source.arithmetic.carrier) :
    E.galois.map (source.projection.map (x * y)) =
      target.projection.map (E.arithmetic.map (x * y)) :=
  E.projection_square (x * y)

end SourceExactSequenceEmbedding

/-! ## 13. Local-data ledger, without collapsing finite and archimedean sides -/

namespace SourceFiniteLocalData

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l}
variable {P : SourcePlacePartition l D}
variable {i : P.finiteIndex}
variable {xGlobal cGlobal : SourceProfiniteExactSequence}
variable (L : SourceFiniteLocalData l D P i xGlobal cGlobal)

theorem global_x_embedding_is_injective :
    Function.Injective L.xGroupEmbedding.geometric.map :=
  L.xGroupEmbedding.geometric_injective

theorem global_c_embedding_is_injective :
    Function.Injective L.cGroupEmbedding.geometric.map :=
  L.cGroupEmbedding.geometric_injective

theorem local_x_decomposition_is_injective :
    Function.Injective L.xLocal_decomposition_embedding.map :=
  L.xLocal_decomposition_injective

theorem local_c_decomposition_is_injective :
    Function.Injective L.cLocal_decomposition_embedding.map :=
  L.cLocal_decomposition_injective

theorem local_x_exactness (x : L.xExactSequence.arithmetic.carrier) :
    L.xExactSequence.projection.map x = 1 ↔
      ∃ y, L.xExactSequence.injection.map y = x :=
  L.xExactSequence.exact_at_arithmetic x

theorem local_c_exactness (x : L.cExactSequence.arithmetic.carrier) :
    L.cExactSequence.projection.map x = 1 ↔
      ∃ y, L.cExactSequence.injection.map y = x :=
  L.cExactSequence.exact_at_arithmetic x

theorem local_x_section (x : L.xExactSequence.galois.carrier) :
    L.xExactSequence.projection.map
      (L.xExactSequence.sectionMap.map x) = x :=
  L.xExactSequence.section_right_inverse x

theorem local_c_section (x : L.cExactSequence.galois.carrier) :
    L.cExactSequence.projection.map
      (L.cExactSequence.sectionMap.map x) = x :=
  L.cExactSequence.section_right_inverse x

theorem local_finite_bundle :
    L.base_change_curve ∧ L.base_change_orbicurve ∧
      L.local_bad_type ∧ L.local_q_parameter := by
  exact ⟨L.base_change_curve_proved, L.base_change_orbicurve_proved,
    L.local_bad_type_proved, L.local_q_parameter_proved⟩

theorem local_finite_signatures :
    L.xLocal_signature ∧ L.cLocal_signature := by
  exact ⟨L.xLocal_signature_proved, L.cLocal_signature_proved⟩

end SourceFiniteLocalData

namespace SourceInfiniteLocalData

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l}
variable {P : SourcePlacePartition l D}
variable {i : P.infiniteIndex}
variable {xGlobal cGlobal : SourceProfiniteExactSequence}
variable (L : SourceInfiniteLocalData l D P i xGlobal cGlobal)

theorem global_x_embedding_is_injective :
    Function.Injective L.xGroupEmbedding.geometric.map :=
  L.xGroupEmbedding.geometric_injective

theorem global_c_embedding_is_injective :
    Function.Injective L.cGroupEmbedding.geometric.map :=
  L.cGroupEmbedding.geometric_injective

theorem local_x_decomposition_is_injective :
    Function.Injective L.xLocal_decomposition_embedding.map :=
  L.xLocal_decomposition_injective

theorem local_c_decomposition_is_injective :
    Function.Injective L.cLocal_decomposition_embedding.map :=
  L.cLocal_decomposition_injective

theorem local_x_exactness (x : L.xExactSequence.arithmetic.carrier) :
    L.xExactSequence.projection.map x = 1 ↔
      ∃ y, L.xExactSequence.injection.map y = x :=
  L.xExactSequence.exact_at_arithmetic x

theorem local_c_exactness (x : L.cExactSequence.arithmetic.carrier) :
    L.cExactSequence.projection.map x = 1 ↔
      ∃ y, L.cExactSequence.injection.map y = x :=
  L.cExactSequence.exact_at_arithmetic x

theorem local_x_section (x : L.xExactSequence.galois.carrier) :
    L.xExactSequence.projection.map
      (L.xExactSequence.sectionMap.map x) = x :=
  L.xExactSequence.section_right_inverse x

theorem local_c_section (x : L.cExactSequence.galois.carrier) :
    L.cExactSequence.projection.map
      (L.cExactSequence.sectionMap.map x) = x :=
  L.cExactSequence.section_right_inverse x

theorem local_infinite_bundle :
    L.base_change_curve ∧ L.base_change_orbicurve ∧
      L.local_archimedean_type ∧ L.local_section_compatibility := by
  exact ⟨L.base_change_curve_proved, L.base_change_orbicurve_proved,
    L.local_archimedean_type_proved,
    L.local_section_compatibility_proved⟩

theorem local_infinite_signatures :
    L.xLocal_signature ∧ L.cLocal_signature := by
  exact ⟨L.xLocal_signature_proved, L.cLocal_signature_proved⟩

end SourceInfiniteLocalData

/-! ## 14. Clause markers and arithmetic-to-source consistency -/

namespace ClauseA

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l} (A : ClauseA l D)
include A

theorem marker_clause_a_field :
    HasSqrtNegOne D.arithmetic.F := A.squareRootNegOne

theorem marker_clause_a_curve :
    D.xF.signature = SourceOrbicurveSignature.typeOneOne :=
  A.curve_is_once_punctured_elliptic

theorem marker_clause_a_stable_for_all :
    ∀ p : NumberField.FinitePlace D.arithmetic.F,
      D.arithmetic.curve.HasStableReductionAt p :=
  A.stable_reduction_everywhere

theorem marker_clause_a_field_moduli : A.field_of_moduli :=
  A.field_of_moduli_proved

theorem marker_clause_a_sign_involution : A.sign_involution_exists :=
  A.sign_involution_exists_proved

theorem marker_clause_a_recovery : A.elliptic_curve_recovery :=
  A.elliptic_curve_recovery_proved

theorem marker_clause_a_moduli_places : A.moduli_place_definition :=
  A.moduli_place_definition_proved

theorem marker_clause_a_closure_field : A.algebraicClosure_field :=
  A.algebraicClosure_field_proved

theorem marker_clause_a_closure_algebraic : A.algebraicClosure_algebraic :=
  A.algebraicClosure_algebraic_proved

theorem marker_clause_a_maximal_solvable
    (E : IntermediateField D.arithmetic.Fmod
      (AlgebraicClosure D.arithmetic.Fmod))
    (hfinite : FiniteDimensional D.arithmetic.Fmod E)
    (hgalois : IsGalois D.arithmetic.Fmod E) :
    E ≤ A.maximal_solvable_extension :=
  A.maximal_solvable_contains E hfinite hgalois

theorem marker_clause_a_all :
    HasSqrtNegOne D.arithmetic.F ∧
      D.xF.signature = SourceOrbicurveSignature.typeOneOne ∧
      (∀ p : NumberField.FinitePlace D.arithmetic.F,
        D.arithmetic.curve.HasStableReductionAt p) ∧
      A.field_of_moduli ∧ A.sign_involution_exists := by
  exact ⟨A.squareRootNegOne, A.curve_is_once_punctured_elliptic,
    A.stable_reduction_everywhere, A.field_of_moduli_proved,
    A.sign_involution_exists_proved⟩

end ClauseA

namespace ClauseB

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l} (B : ClauseB l D)
include B

theorem marker_clause_b_nonempty : D.VbadMod.Nonempty := B.bad_nonempty

theorem marker_clause_b_odd
    (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  B.bad_odd_residue_characteristic p hp

theorem marker_clause_b_selected
    (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) : NumberFieldPlace.finite p ∈ D.Vmod :=
  B.bad_subset_selected p hp

theorem marker_clause_b_multiplicative
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    D.arithmetic.curve.HasMultiplicativeReductionAt p :=
  B.multiplicative_over_bad p hp

theorem marker_clause_b_stable
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    D.arithmetic.curve.HasStableReductionAt p :=
  B.stable_over_bad p hp

theorem marker_clause_b_q
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    NumberFieldFinitePlace.FinitePlaceQCandidate p := B.qParameter p hp

theorem marker_clause_b_q_order
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    0 < (B.qParameter p hp).order := (B.qParameter p hp).order_pos

theorem marker_clause_b_q_ne_one
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    (B.qParameter p hp).q ≠ 1 := (B.qParameter p hp).q_ne_one

theorem marker_clause_b_q_ne_zero
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    (B.qParameter p hp).q ≠ 0 := (B.qParameter p hp).valuation_ne_zero

theorem marker_clause_b_q_coprime
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    Nat.Coprime (B.qParameter p hp).order l.value :=
  B.q_order_prime_to_l p hp

theorem marker_clause_b_reduction_bundle
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    D.arithmetic.curve.HasStableReductionAt p ∧
      D.arithmetic.curve.HasMultiplicativeReductionAt p ∧
      Nat.Coprime (B.qParameter p hp).order l.value := by
  exact ⟨B.stable_over_bad p hp, B.multiplicative_over_bad p hp,
    B.q_order_prime_to_l p hp⟩

theorem marker_clause_b_residue_pos
    (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) :
    0 < NumberFieldFinitePlace.residueCharacteristic p :=
  (NumberFieldFinitePlace.residueCharacteristic_prime p).pos

theorem marker_clause_b_all :
    D.VbadMod.Nonempty ∧
      (∀ p : NumberField.FinitePlace D.arithmetic.Fmod,
        p ∈ D.VbadMod →
          Odd (NumberFieldFinitePlace.residueCharacteristic p)) ∧
      (∀ p hp, D.arithmetic.curve.HasMultiplicativeReductionAt p) := by
  exact ⟨B.bad_nonempty, B.bad_odd_residue_characteristic,
    B.multiplicative_over_bad⟩

end ClauseB

namespace ClauseC

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l} (C : ClauseC l D)
include C

theorem marker_clause_c_l_prime : Nat.Prime l.value := l.prime

theorem marker_clause_c_l_ge_five : 5 ≤ l.value := l.ge_five

theorem marker_clause_c_l_odd : Odd l.value := l.odd

theorem marker_clause_c_torsion23 :
    PuncturedEllipticCurve.Torsion23Rational D.arithmetic.curve :=
  C.torsion23_rational

theorem marker_clause_c_basis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      D.arithmetic.curve.LTorsion l := C.torsion_module_basis

theorem marker_clause_c_representation :
    C.galois_representation =
      D.arithmetic.curve.galoisLTorsionMatrixRepresentation
        l C.torsion_module_basis := C.galois_representation_eq_canonical

theorem marker_clause_c_image :
    C.standard_SL2_image ≤ C.galois_representation.range :=
  C.image_contains_SL2

theorem marker_clause_c_kernel : C.K_kernel_field_compatibility :=
  C.K_kernel_field_compatibility_proved

theorem marker_clause_c_residue_coprime
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    Nat.Coprime l.value
      (NumberFieldFinitePlace.residueCharacteristic
        (NumberFieldFinitePlace.comap p)) :=
  C.l_prime_to_bad_residue_characteristics p hp

theorem marker_clause_c_q_coprime
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    Nat.Coprime l.value (C.q_order p hp) := C.l_prime_to_q_orders p hp

theorem marker_clause_c_finite_galois : C.kernel_field_finite_galois :=
  C.kernel_field_finite_galois_proved

theorem marker_clause_c_continuous : C.torsion_action_continuous :=
  C.torsion_action_continuous_proved

theorem marker_clause_c_all :
    C.torsion23_rational ∧
      C.standard_SL2_image ≤ C.galois_representation.range ∧
      C.K_kernel_field_compatibility ∧
      C.kernel_field_finite_galois ∧ C.torsion_action_continuous := by
  exact ⟨C.torsion23_rational, C.image_contains_SL2,
    C.K_kernel_field_compatibility_proved,
    C.kernel_field_finite_galois_proved,
    C.torsion_action_continuous_proved⟩

end ClauseC

namespace ClauseD

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l} (C : ClauseD l D)
include C

theorem marker_clause_d_xF :
    D.xF.signature = SourceOrbicurveSignature.typeOneOne := C.xF_type

theorem marker_clause_d_cF :
    D.cF.signature = SourceOrbicurveSignature.typeOneOne := C.cF_type

theorem marker_clause_d_xK :
    D.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l := C.xK_type

theorem marker_clause_d_cK :
    D.cK.signature = SourceOrbicurveSignature.typeOneLTorsionPlusMinus l :=
  C.cK_type

theorem marker_clause_d_involution : C.signInvolution_squared :=
  C.signInvolution_squared_proved

theorem marker_clause_d_quotient : C.signQuotient_invariant :=
  C.signQuotient_invariant_proved

theorem marker_clause_d_cover : C.xK_cK_cover.finite_etale :=
  C.xK_cK_cover_finite_etale

theorem marker_clause_d_cartesian : C.xK_cK_cartesian_square :=
  C.xK_cK_cartesian_square_proved

theorem marker_clause_d_delta_x : C.delta_x_open_subgroup :=
  C.delta_x_open_subgroup_proved

theorem marker_clause_d_delta_c : C.delta_c_open_subgroup :=
  C.delta_c_open_subgroup_proved

theorem marker_clause_d_naturality : C.group_diagram_naturality :=
  C.group_diagram_naturality_proved

theorem marker_clause_d_exact_x :
    Function.Surjective C.xF_exact_sequence.projection.map ∧
      Function.Injective C.xF_exact_sequence.injection.map := by
  exact ⟨C.xF_exact_sequence.projection_surjective,
    C.xF_exact_sequence.injection_injective⟩

theorem marker_clause_d_exact_c :
    Function.Surjective C.cF_exact_sequence.projection.map ∧
      Function.Injective C.cF_exact_sequence.injection.map := by
  exact ⟨C.cF_exact_sequence.projection_surjective,
    C.cF_exact_sequence.injection_injective⟩

theorem marker_clause_d_all :
    D.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l ∧
      D.cK.signature = SourceOrbicurveSignature.typeOneLTorsionPlusMinus l ∧
      C.xK_cK_cartesian_square ∧ C.delta_x_open_subgroup ∧
      C.delta_c_open_subgroup := by
  exact ⟨C.xK_type, C.cK_type,
    C.xK_cK_cartesian_square_proved,
    C.delta_x_open_subgroup_proved,
    C.delta_c_open_subgroup_proved⟩

end ClauseD

namespace ClauseE

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l}
variable {C : ClauseD l D} (E : ClauseE l D C)
include E

theorem marker_clause_e_partition : SourcePlacePartition l D :=
  E.placePartition

theorem marker_clause_e_section : E.V_is_section := E.V_is_section_proved

theorem marker_clause_e_finite_curve : E.finite_local_curve_diagram :=
  E.finite_local_curve_diagram_proved

theorem marker_clause_e_infinite_curve : E.infinite_local_curve_diagram :=
  E.infinite_local_curve_diagram_proved

theorem marker_clause_e_decomposition : E.decomposition_group_naturality :=
  E.decomposition_group_naturality_proved

theorem marker_clause_e_projection :
    E.local_group_projection_compatibility :=
  E.local_group_projection_compatibility_proved

theorem marker_clause_e_finite_family :
    ∀ i : E.placePartition.finiteIndex,
      SourceFiniteLocalData l D E.placePartition i
        C.xF_exact_sequence C.cF_exact_sequence := E.finiteLocal

theorem marker_clause_e_infinite_family :
    ∀ i : E.placePartition.infiniteIndex,
      SourceInfiniteLocalData l D E.placePartition i
        C.xF_exact_sequence C.cF_exact_sequence := E.infiniteLocal

theorem marker_clause_e_bad_type
    (i : E.placePartition.finiteIndex)
    (h : D.placeToMod (E.placePartition.finiteToV i) ∈ D.VbadMod) :
    E.bad_local_orbicurve_type i h := E.bad_local_orbicurve_type_proved i h

theorem marker_clause_e_good_type
    (i : E.placePartition.finiteIndex)
    (h : D.placeToMod (E.placePartition.finiteToV i) ∉ D.VbadMod) :
    E.good_local_orbicurve_type i h := E.good_local_orbicurve_type_proved i h

theorem marker_clause_e_partition_bijective :
    Function.Bijective
      (Sum.elim E.placePartition.finiteToV E.placePartition.infiniteToV) :=
  E.placePartition.kindPartition

theorem marker_clause_e_finite_place
    (i : E.placePartition.finiteIndex) :
    D.place (E.placePartition.finiteToV i) =
      NumberFieldPlace.finite (E.placePartition.finitePlace i) :=
  E.placePartition.finite_place_compatibility i

theorem marker_clause_e_infinite_place
    (i : E.placePartition.infiniteIndex) :
    D.place (E.placePartition.infiniteToV i) =
      NumberFieldPlace.infinite (E.placePartition.infinitePlace i) :=
  E.placePartition.infinite_place_compatibility i

theorem marker_clause_e_finite_moduli
    (i : E.placePartition.finiteIndex) :
    D.placeToMod (E.placePartition.finiteToV i) =
      NumberFieldPlace.finite
        (NumberFieldFinitePlace.comap (E.placePartition.finitePlace i)) :=
  E.placePartition.finite_moduli_compatibility i

theorem marker_clause_e_infinite_moduli
    (i : E.placePartition.infiniteIndex) :
    D.placeToMod (E.placePartition.infiniteToV i) =
      NumberFieldPlace.infinite
        ((E.placePartition.infinitePlace i).comap
          (algebraMap D.arithmetic.Fmod D.arithmetic.K)) :=
  E.placePartition.infinite_moduli_compatibility i

theorem marker_clause_e_every_place (v : D.V) :
    (∃ i, E.placePartition.finiteToV i = v) ∨
      (∃ i, E.placePartition.infiniteToV i = v) := by
  exact E.placePartition.every_selected_place_is_finite_or_infinite v

theorem marker_clause_e_all :
    E.V_is_section ∧ E.finite_local_curve_diagram ∧
      E.infinite_local_curve_diagram ∧
      E.decomposition_group_naturality ∧
      E.local_group_projection_compatibility := by
  exact ⟨E.V_is_section_proved,
    E.finite_local_curve_diagram_proved,
    E.infinite_local_curve_diagram_proved,
    E.decomposition_group_naturality_proved,
    E.local_group_projection_compatibility_proved⟩

end ClauseE

namespace ClauseF

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l}
variable {C : ClauseD l D} (F : ClauseF l D C)
include F

theorem marker_clause_f_cusp : SourceCuspDatum := F.cusp

theorem marker_clause_f_nonzero : F.cusp.nonzero_quotient :=
  F.cusp.nonzero_quotient_proved

theorem marker_clause_f_canonical : F.cusp.canonical_generator :=
  F.cusp.canonical_generator_proved

theorem marker_clause_f_sign : F.cusp.sign_ambiguity :=
  F.cusp.sign_ambiguity_proved

theorem marker_clause_f_on_cK : F.cusp_lies_on_cK :=
  F.cusp_lies_on_cK_proved

theorem marker_clause_f_from_Q : F.cusp_from_nonzero_Q :=
  F.cusp_from_nonzero_Q_proved

theorem marker_clause_f_localization (v : D.V) : F.cusp_localization v :=
  F.cusp_localization_proved v

theorem marker_clause_f_bad
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    F.bad_cusp_canonical_generator p hp :=
  F.bad_cusp_canonical_generator_proved p hp

theorem marker_clause_f_good
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∉ D.VbadMod) :
    F.good_cusp_compatibility p hp :=
  F.good_cusp_compatibility_proved p hp

theorem marker_clause_f_sign_independence : F.cusp_sign_independence :=
  F.cusp_sign_independence_proved

theorem marker_clause_f_diagram : F.cusp_diagram_compatibility :=
  F.cusp_diagram_compatibility_proved

theorem marker_clause_f_all :
    F.cusp_lies_on_cK ∧ F.cusp_from_nonzero_Q ∧
      F.cusp_sign_independence ∧ F.cusp_diagram_compatibility := by
  exact ⟨F.cusp_lies_on_cK_proved, F.cusp_from_nonzero_Q_proved,
    F.cusp_sign_independence_proved,
    F.cusp_diagram_compatibility_proved⟩

end ClauseF

namespace SourceInitialThetaData

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

theorem marker_initial_theta_data : InitialThetaDataConclusion S :=
  S.conclusion

theorem marker_initial_theta_data_a :
    HasSqrtNegOne S.candidate.arithmetic.F :=
  S.clauseA.squareRootNegOne

theorem marker_initial_theta_data_b : S.candidate.VbadMod.Nonempty :=
  S.clauseB.bad_nonempty

theorem marker_initial_theta_data_c :
    PuncturedEllipticCurve.Torsion23Rational S.candidate.arithmetic.curve :=
  S.clauseC.torsion23_rational

theorem marker_initial_theta_data_d :
    S.candidate.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l :=
  S.clauseD.xK_type

theorem marker_initial_theta_data_e : S.clauseE.V_is_section :=
  S.clauseE.V_is_section_proved

theorem marker_initial_theta_data_f : S.clauseF.cusp.nonzero_quotient :=
  S.clauseF.cusp.nonzero_quotient_proved

theorem marker_initial_theta_data_arithmetic_coherence :
    S.arithmetic_clause_coherence := S.arithmetic_clause_coherence_proved

theorem marker_initial_theta_data_order_coherence :
    S.clause_order_coherence := S.clause_order_coherence_proved

theorem marker_initial_theta_data_candidate :
    S.candidate = S.candidate := rfl

theorem marker_initial_theta_data_clause_records :
    ClauseA l S.candidate ∧ ClauseB l S.candidate ∧
      ClauseC l S.candidate ∧ ClauseD l S.candidate ∧
      ClauseE l S.candidate S.clauseD ∧
      ClauseF l S.candidate S.clauseD :=
  S.all_six_clause_records

theorem marker_initial_theta_data_place_bijection :
    Function.Bijective S.candidate.placeToMod :=
  S.candidate.placeToMod_bijective

theorem marker_initial_theta_data_place_section (v : S.candidate.V) :
    NumberFieldPlace.comap (S.candidate.place v) =
      S.candidate.placeToMod v := S.candidate.place_comap_compatible v

theorem marker_initial_theta_data_place_membership (v : S.candidate.V) :
    S.candidate.placeToMod v ∈ S.candidate.Vmod :=
  S.candidate.placeToMod_mem_Vmod v

theorem marker_initial_theta_data_bad_subset
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.finite p ∈ S.candidate.Vmod :=
  S.candidate.badMod_subset_Vmod p hp

theorem marker_initial_theta_data_q
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    Nat.Coprime (S.clauseB.qParameter p hp).order l.value :=
  S.clauseB.q_order_prime_to_l p hp

theorem marker_initial_theta_data_stable
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.candidate.arithmetic.curve.HasStableReductionAt p :=
  S.clauseB.stable_over_bad p hp

theorem marker_initial_theta_data_multiplicative
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p :=
  S.clauseB.multiplicative_over_bad p hp

theorem marker_initial_theta_data_torsion_image :
    S.clauseC.standard_SL2_image ≤ S.clauseC.galois_representation.range :=
  S.clauseC.image_contains_SL2

theorem marker_initial_theta_data_xK_cK_cartesian :
    S.clauseD.xK_cK_cartesian_square :=
  S.clauseD.xK_cK_cartesian_square_proved

theorem marker_initial_theta_data_cusp_canonical :
    S.clauseF.cusp.canonical_generator :=
  S.clauseF.cusp.canonical_generator_proved

theorem marker_initial_theta_data_cusp_compatible :
    S.clauseF.cusp_diagram_compatibility :=
  S.clauseF.cusp_diagram_compatibility_proved

theorem marker_initial_theta_data_universal :
    ∀ p : NumberField.FinitePlace S.candidate.arithmetic.F,
      S.candidate.arithmetic.curve.HasStableReductionAt p :=
  S.clauseA.stable_reduction_everywhere

theorem marker_initial_theta_data_local_finite_universal :
    ∀ i : S.clauseE.placePartition.finiteIndex,
      SourceFiniteLocalData l S.candidate S.clauseE.placePartition i
        S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence :=
  S.clauseE.finiteLocal

theorem marker_initial_theta_data_local_infinite_universal :
    ∀ i : S.clauseE.placePartition.infiniteIndex,
      SourceInfiniteLocalData l S.candidate S.clauseE.placePartition i
        S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence :=
  S.clauseE.infiniteLocal

end SourceInitialThetaData

namespace SourceInitialThetaCandidate

variable {l : PrimeGeFive} (D : SourceInitialThetaCandidate l)

theorem arithmetic_spec : D.arithmetic = D.arithmetic := rfl

theorem arithmetic_prime_field_spec :
    Nat.Prime l.value := l.prime

theorem arithmetic_prime_lower_bound : 5 ≤ l.value := l.ge_five

theorem arithmetic_prime_odd : Odd l.value := l.odd

theorem arithmetic_sqrt_neg_one :
    HasSqrtNegOne D.arithmetic.F :=
  D.arithmetic.tower.sqrtNegOne

theorem arithmetic_degree_prime_to_l :
    Nat.Coprime (Module.finrank D.arithmetic.Fmod D.arithmetic.F) l.value :=
  D.arithmetic.tower.degreePrimeToL

theorem arithmetic_curve_spec :
    D.arithmetic.curve = D.arithmetic.curve := rfl

theorem arithmetic_Fmod_spec : D.arithmetic.Fmod = D.arithmetic.Fmod := rfl

theorem arithmetic_F_spec : D.arithmetic.F = D.arithmetic.F := rfl

theorem arithmetic_K_spec : D.arithmetic.K = D.arithmetic.K := rfl

theorem arithmetic_galois_Fmod_F :
    IsGalois D.arithmetic.Fmod D.arithmetic.F := inferInstance

theorem arithmetic_galois_F_K :
    IsGalois D.arithmetic.F D.arithmetic.K := inferInstance

theorem arithmetic_finite_Fmod_F :
    FiniteDimensional D.arithmetic.Fmod D.arithmetic.F := inferInstance

theorem arithmetic_finite_F_K :
    FiniteDimensional D.arithmetic.F D.arithmetic.K := inferInstance

theorem arithmetic_place_map_surjective :
    Function.Surjective D.placeToMod := D.placeToMod_bijective.surjective

theorem arithmetic_place_map_injective :
    Function.Injective D.placeToMod := D.placeToMod_bijective.injective

theorem arithmetic_place_map_bijective :
    Function.Bijective D.placeToMod := D.placeToMod_bijective

theorem arithmetic_place_map_mem (v : D.V) :
    D.placeToMod v ∈ D.Vmod := D.placeToMod_mem_Vmod v

theorem arithmetic_place_comap (v : D.V) :
    NumberFieldPlace.comap (D.place v) = D.placeToMod v :=
  D.place_comap_compatible v

theorem arithmetic_bad_subset
    (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) : NumberFieldPlace.finite p ∈ D.Vmod :=
  D.badMod_subset_Vmod p hp

theorem arithmetic_candidate_epsilon : D.epsilon = D.epsilon := rfl

theorem arithmetic_candidate_place :
    D.place = D.place := rfl

theorem arithmetic_candidate_placeToMod :
    D.placeToMod = D.placeToMod := rfl

theorem arithmetic_candidate_Vmod : D.Vmod = D.Vmod := rfl

theorem arithmetic_candidate_VbadMod : D.VbadMod = D.VbadMod := rfl

theorem arithmetic_candidate_xF : D.xF = D.xF := rfl

theorem arithmetic_candidate_cF : D.cF = D.cF := rfl

theorem arithmetic_candidate_xK : D.xK = D.xK := rfl

theorem arithmetic_candidate_cK : D.cK = D.cK := rfl

end SourceInitialThetaCandidate
-/

/-! ## 3. Clause (a): fields, curves, and moduli -/

structure ClauseA (l : PrimeGeFive)
    (D : SourceInitialThetaCandidate l) where
  squareRootNegOne : HasSqrtNegOne D.arithmetic.F
  algebraicClosure_field : Prop
  algebraicClosure_field_proved : algebraicClosure_field
  algebraicClosure_algebraic : Prop
  algebraicClosure_algebraic_proved : algebraicClosure_algebraic
  curve_is_once_punctured_elliptic :
    D.xF.signature = SourceOrbicurveSignature.typeOneOne
  curve_realization : Prop
  curve_realization_proved : curve_realization
  stable_reduction_everywhere :
    ∀ p : NumberField.FinitePlace D.arithmetic.F,
      D.arithmetic.curve.HasStableReductionAt p
  elliptic_curve_recovery : Prop
  elliptic_curve_recovery_proved : elliptic_curve_recovery
  sign_involution_exists : Prop
  sign_involution_exists_proved : sign_involution_exists
  field_of_moduli : Prop
  field_of_moduli_proved : field_of_moduli
  maximal_solvable_extension :
    IntermediateField D.arithmetic.Fmod
      (AlgebraicClosure D.arithmetic.Fmod)
  maximal_solvable_contains :
    ∀ E : IntermediateField D.arithmetic.Fmod
      (AlgebraicClosure D.arithmetic.Fmod),
      FiniteDimensional D.arithmetic.Fmod E →
        IsGalois D.arithmetic.Fmod E →
        E ≤ maximal_solvable_extension
  moduli_place_definition : Prop
  moduli_place_definition_proved : moduli_place_definition

namespace ClauseA

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l} (A : ClauseA l D)
include A

theorem sqrtNegOne_spec : HasSqrtNegOne D.arithmetic.F :=
  A.squareRootNegOne

theorem algebraicClosure_field_spec : A.algebraicClosure_field :=
  A.algebraicClosure_field_proved

theorem algebraicClosure_algebraic_spec : A.algebraicClosure_algebraic :=
  A.algebraicClosure_algebraic_proved

theorem curve_signature_spec :
    D.xF.signature = SourceOrbicurveSignature.typeOneOne :=
  A.curve_is_once_punctured_elliptic

theorem curve_realization_spec : A.curve_realization :=
  A.curve_realization_proved

theorem stable_reduction_spec (p : NumberField.FinitePlace D.arithmetic.F) :
    D.arithmetic.curve.HasStableReductionAt p :=
  A.stable_reduction_everywhere p

theorem elliptic_curve_recovery_spec : A.elliptic_curve_recovery :=
  A.elliptic_curve_recovery_proved

theorem sign_involution_spec : A.sign_involution_exists :=
  A.sign_involution_exists_proved

theorem field_of_moduli_spec : A.field_of_moduli :=
  A.field_of_moduli_proved

theorem maximal_solvable_contains_spec
    (E : IntermediateField D.arithmetic.Fmod
      (AlgebraicClosure D.arithmetic.Fmod))
    (hfinite : FiniteDimensional D.arithmetic.Fmod E)
    (hgalois : IsGalois D.arithmetic.Fmod E) :
    E ≤ A.maximal_solvable_extension :=
  A.maximal_solvable_contains E hfinite hgalois

theorem moduli_place_definition_spec : A.moduli_place_definition :=
  A.moduli_place_definition_proved

theorem field_clause_bundle :
    HasSqrtNegOne D.arithmetic.F ∧
      D.xF.signature = SourceOrbicurveSignature.typeOneOne ∧
      (∀ p : NumberField.FinitePlace D.arithmetic.F,
        D.arithmetic.curve.HasStableReductionAt p) ∧
      A.field_of_moduli := by
  exact ⟨A.squareRootNegOne, A.curve_is_once_punctured_elliptic,
    A.stable_reduction_everywhere, A.field_of_moduli_proved⟩

theorem field_clause_bundle_extended :
    (HasSqrtNegOne D.arithmetic.F ∧
      D.xF.signature = SourceOrbicurveSignature.typeOneOne ∧
      (∀ p : NumberField.FinitePlace D.arithmetic.F,
        D.arithmetic.curve.HasStableReductionAt p) ∧
      A.field_of_moduli) ∧
      A.algebraicClosure_field ∧ A.algebraicClosure_algebraic ∧
      A.curve_realization ∧ A.elliptic_curve_recovery ∧
      A.sign_involution_exists ∧ A.moduli_place_definition := by
  exact ⟨A.field_clause_bundle, A.algebraicClosure_field_proved,
    A.algebraicClosure_algebraic_proved, A.curve_realization_proved,
    A.elliptic_curve_recovery_proved, A.sign_involution_exists_proved,
    A.moduli_place_definition_proved⟩

end ClauseA

/-! ## 4. Clause (b): bad places, reduction, and local q-parameters -/

structure ClauseB (l : PrimeGeFive)
    (D : SourceInitialThetaCandidate l) where
  bad_nonempty : D.VbadMod.Nonempty
  bad_is_finite : ∀ p, p ∈ D.VbadMod →
    NumberFieldPlace.IsFinite (NumberFieldPlace.finite p)
  bad_odd_residue_characteristic :
    ∀ p : NumberField.FinitePlace D.arithmetic.Fmod,
      p ∈ D.VbadMod →
      Odd (NumberFieldFinitePlace.residueCharacteristic p)
  bad_subset_selected : ∀ p, p ∈ D.VbadMod →
    NumberFieldPlace.finite p ∈ D.Vmod
  multiplicative_over_bad :
    ∀ p : NumberField.FinitePlace D.arithmetic.F,
      NumberFieldFinitePlace.comap p ∈ D.VbadMod →
      D.arithmetic.curve.HasMultiplicativeReductionAt p
  stable_over_bad :
    ∀ p : NumberField.FinitePlace D.arithmetic.F,
      NumberFieldFinitePlace.comap p ∈ D.VbadMod →
      D.arithmetic.curve.HasStableReductionAt p
  qParameter :
    ∀ (p : NumberField.FinitePlace D.arithmetic.F),
      NumberFieldFinitePlace.comap p ∈ D.VbadMod →
      NumberFieldFinitePlace.FinitePlaceQCandidate p
  q_order_prime_to_l :
    ∀ (p : NumberField.FinitePlace D.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod),
      Nat.Coprime (qParameter p hp).order l.value
  q_parameter_realizes_curve :
    ∀ (p : NumberField.FinitePlace D.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod),
      Prop
  q_parameter_realizes_curve_proved :
    ∀ (p : NumberField.FinitePlace D.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod),
      q_parameter_realizes_curve p hp
  reduction_base_change_compatibility : Prop
  reduction_base_change_compatibility_proved : reduction_base_change_compatibility

namespace ClauseB

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l} (B : ClauseB l D)
include B

theorem bad_nonempty_spec : D.VbadMod.Nonempty := B.bad_nonempty

theorem bad_is_finite_spec
    (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) :
    NumberFieldPlace.IsFinite (NumberFieldPlace.finite p) :=
  B.bad_is_finite p hp

theorem bad_odd_residue_characteristic_spec
    (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  B.bad_odd_residue_characteristic p hp

theorem bad_subset_selected_spec
    (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) :
    NumberFieldPlace.finite p ∈ D.Vmod :=
  B.bad_subset_selected p hp

theorem multiplicative_over_bad_spec
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    D.arithmetic.curve.HasMultiplicativeReductionAt p :=
  B.multiplicative_over_bad p hp

theorem stable_over_bad_spec
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    D.arithmetic.curve.HasStableReductionAt p :=
  B.stable_over_bad p hp

def qParameter_spec
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    NumberFieldFinitePlace.FinitePlaceQCandidate p :=
  B.qParameter p hp

theorem q_order_prime_to_l_spec
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    Nat.Coprime (B.qParameter p hp).order l.value :=
  B.q_order_prime_to_l p hp

theorem q_parameter_realizes_curve_spec
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    B.q_parameter_realizes_curve p hp :=
  B.q_parameter_realizes_curve_proved p hp

theorem reduction_base_change_spec :
    B.reduction_base_change_compatibility :=
  B.reduction_base_change_compatibility_proved

theorem bad_residue_characteristic_pos
    (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) :
    0 < NumberFieldFinitePlace.residueCharacteristic p :=
  (NumberFieldFinitePlace.residueCharacteristic_prime p).pos

theorem bad_residue_characteristic_ne_zero
    (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) :
    NumberFieldFinitePlace.residueCharacteristic p ≠ 0 :=
  Nat.ne_of_gt (B.bad_residue_characteristic_pos p hp)

theorem bad_reduction_bundle
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    D.arithmetic.curve.HasStableReductionAt p ∧
      D.arithmetic.curve.HasMultiplicativeReductionAt p ∧
      Nat.Coprime (B.qParameter p hp).order l.value := by
  exact ⟨B.stable_over_bad p hp, B.multiplicative_over_bad p hp,
    B.q_order_prime_to_l p hp⟩

theorem bad_q_order_pos
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    0 < (B.qParameter p hp).order :=
  (B.qParameter p hp).order_pos

theorem bad_q_ne_one
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    (B.qParameter p hp).q ≠ 1 :=
  (B.qParameter p hp).q_ne_one

theorem bad_q_nonzero
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
  (B.qParameter p hp).q ≠ 0 :=
  (B.qParameter p hp).q_ne_zero

theorem bad_place_is_selected
    (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) :
    NumberFieldPlace.finite p ∈ D.Vmod :=
  B.bad_subset_selected_spec p hp

theorem bad_nonempty_has_member :
    ∃ p : NumberField.FinitePlace D.arithmetic.Fmod, p ∈ D.VbadMod :=
  B.bad_nonempty

theorem bad_odd_implies_not_two
    (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) :
    NumberFieldFinitePlace.residueCharacteristic p ≠ 2 := by
  intro htwo
  have hodd := B.bad_odd_residue_characteristic_spec p hp
  rw [htwo] at hodd
  norm_num at hodd

theorem stable_follows_from_multiplicative
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    D.arithmetic.curve.HasStableReductionAt p :=
  PuncturedEllipticCurve.hasMultiplicativeReductionAt_imp_stable
    (B.multiplicative_over_bad p hp)

end ClauseB

/-! ## 5. Clause (c): torsion, the mod-l image, and the field K -/

structure ClauseC (l : PrimeGeFive)
    (D : SourceInitialThetaCandidate l) where
  torsion23_rational :
    PuncturedEllipticCurve.Torsion23Rational D.arithmetic.curve
  torsion_module_basis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      D.arithmetic.curve.LTorsion l
  galois_representation :
    (AlgebraicClosure D.arithmetic.F ≃ₐ[D.arithmetic.F]
      AlgebraicClosure D.arithmetic.F) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)
  galois_representation_eq_canonical :
    galois_representation =
      D.arithmetic.curve.galoisLTorsionMatrixRepresentation
        l torsion_module_basis
  standard_SL2_image :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))
  standard_SL2_image_spec : Prop
  standard_SL2_image_spec_proved : standard_SL2_image_spec
  image_contains_SL2 :
    standard_SL2_image ≤ galois_representation.range
  K_kernel_field_compatibility : Prop
  K_kernel_field_compatibility_proved : K_kernel_field_compatibility
  l_prime_to_bad_residue_characteristics :
    ∀ (p : NumberField.FinitePlace D.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod),
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := D.arithmetic.Fmod) p))
  q_order :
    ∀ (p : NumberField.FinitePlace D.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod), Nat
  l_prime_to_q_orders :
    ∀ (p : NumberField.FinitePlace D.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod),
      Nat.Coprime l.value (q_order p hp)
  kernel_field_finite_galois : Prop
  kernel_field_finite_galois_proved : kernel_field_finite_galois
  torsion_action_continuous : Prop
  torsion_action_continuous_proved : torsion_action_continuous

namespace ClauseC

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l} (C : ClauseC l D)
include C

theorem torsion23_rational_spec :
    PuncturedEllipticCurve.Torsion23Rational D.arithmetic.curve :=
  C.torsion23_rational

def torsion_basis_spec :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      D.arithmetic.curve.LTorsion l :=
  C.torsion_module_basis

def galois_representation_spec :
    (AlgebraicClosure D.arithmetic.F ≃ₐ[D.arithmetic.F]
      AlgebraicClosure D.arithmetic.F) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  C.galois_representation

theorem galois_representation_canonical :
    C.galois_representation =
      D.arithmetic.curve.galoisLTorsionMatrixRepresentation
        l C.torsion_module_basis :=
  C.galois_representation_eq_canonical

theorem standard_SL2_image_prop_spec : C.standard_SL2_image_spec :=
  C.standard_SL2_image_spec_proved

theorem image_contains_SL2_spec :
    C.standard_SL2_image ≤ C.galois_representation.range :=
  C.image_contains_SL2

theorem K_kernel_field_compatibility_spec :
    C.K_kernel_field_compatibility :=
  C.K_kernel_field_compatibility_proved

theorem l_prime_to_bad_residue_characteristics_spec
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
      Nat.Coprime l.value
      (NumberFieldFinitePlace.residueCharacteristic
        (NumberFieldFinitePlace.comap (k := D.arithmetic.Fmod) p)) :=
  C.l_prime_to_bad_residue_characteristics p hp

theorem l_prime_to_q_orders_spec
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    Nat.Coprime l.value
      (C.q_order p hp) :=
  C.l_prime_to_q_orders p hp

theorem kernel_field_finite_galois_spec : C.kernel_field_finite_galois :=
  C.kernel_field_finite_galois_proved

theorem torsion_action_continuous_spec : C.torsion_action_continuous :=
  C.torsion_action_continuous_proved

theorem l_is_prime : Nat.Prime l.value := l.prime

theorem l_ge_five : 5 ≤ l.value := l.ge_five

theorem l_is_odd : Odd l.value := l.odd

theorem torsion23_bundle :
    PuncturedEllipticCurve.Torsion23Rational D.arithmetic.curve ∧
      C.standard_SL2_image_spec ∧
      C.K_kernel_field_compatibility ∧ C.kernel_field_finite_galois := by
  exact ⟨C.torsion23_rational, C.standard_SL2_image_spec_proved,
    C.K_kernel_field_compatibility_proved,
    C.kernel_field_finite_galois_proved⟩

theorem representation_is_hom :
    ∀ x y, C.galois_representation (x * y) =
      C.galois_representation x * C.galois_representation y := by
  intro x y
  exact C.galois_representation.map_mul x y

theorem representation_maps_one :
    C.galois_representation 1 = 1 :=
  C.galois_representation.map_one

theorem representation_kernel_mem
    (x : AlgebraicClosure D.arithmetic.F ≃ₐ[D.arithmetic.F]
      AlgebraicClosure D.arithmetic.F)
    (hx : C.galois_representation x = 1) :
    x ∈ C.galois_representation.ker :=
  hx

theorem representation_range_mem
    (x : AlgebraicClosure D.arithmetic.F ≃ₐ[D.arithmetic.F]
      AlgebraicClosure D.arithmetic.F) :
    C.galois_representation x ∈ C.galois_representation.range :=
  ⟨x, rfl⟩

theorem image_contains_SL2_mem
    (g : C.standard_SL2_image) :
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) ∈
      C.galois_representation.range :=
  C.image_contains_SL2 g.property

theorem torsion_basis_two_dimensional :
    Nonempty ((Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      D.arithmetic.curve.LTorsion l) :=
  ⟨C.torsion_module_basis⟩

theorem representation_canonical_apply
    (sigma : AlgebraicClosure D.arithmetic.F ≃ₐ[D.arithmetic.F]
      AlgebraicClosure D.arithmetic.F) :
    C.galois_representation sigma =
      D.arithmetic.curve.galoisLTorsionMatrixRepresentation
        l C.torsion_module_basis sigma := by
  rw [C.galois_representation_eq_canonical]

theorem l_coprime_residue_bundle
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
        (NumberFieldFinitePlace.comap (k := D.arithmetic.Fmod) p)) ∧
      l.value ≥ 5 := by
  exact ⟨C.l_prime_to_bad_residue_characteristics p hp, l.ge_five⟩

theorem source_c_clause_bundle :
    PuncturedEllipticCurve.Torsion23Rational D.arithmetic.curve ∧
      C.standard_SL2_image ≤ C.galois_representation.range ∧
      C.K_kernel_field_compatibility ∧
      C.kernel_field_finite_galois ∧
      C.torsion_action_continuous := by
  exact ⟨C.torsion23_rational, C.image_contains_SL2,
    C.K_kernel_field_compatibility_proved,
    C.kernel_field_finite_galois_proved,
    C.torsion_action_continuous_proved⟩

end ClauseC

/-! ## 6. Clause (d): the K-level orbicurves and exact sequences -/

structure SourceOrbicurveMorphism
    {F : Type u} [Field F]
    (X Y : SourceOrbicurveObject F) where
  map : X.carrier → Y.carrier
  map_structure : Prop
  map_structure_proved : map_structure
  finite_etale : Prop
  finite_etale_proved : finite_etale

namespace SourceOrbicurveMorphism

variable {F : Type u} [Field F]
variable {X Y : SourceOrbicurveObject F}

theorem map_structure_spec (f : SourceOrbicurveMorphism X Y) :
    f.map_structure := f.map_structure_proved

theorem finite_etale_spec (f : SourceOrbicurveMorphism X Y) :
    f.finite_etale := f.finite_etale_proved

theorem map_self_eq (f : SourceOrbicurveMorphism X X) :
    f.map = f.map := rfl

end SourceOrbicurveMorphism

/-! A map between orbicurves over different fields.  The source definition
    uses the base-change maps from the K-level objects to their F-level
    counterparts, so those maps must not be forced into a same-field type. -/

structure SourceOrbicurveCrossFieldMorphism
    {F G : Type u} [Field F] [Field G]
    (X : SourceOrbicurveObject F)
    (Y : SourceOrbicurveObject G) where
  map : X.carrier → Y.carrier
  map_structure : Prop
  map_structure_proved : map_structure
  finite_etale : Prop
  finite_etale_proved : finite_etale

namespace SourceOrbicurveCrossFieldMorphism

variable {F G : Type u} [Field F] [Field G]
variable {X : SourceOrbicurveObject F} {Y : SourceOrbicurveObject G}

theorem map_structure_spec (f : SourceOrbicurveCrossFieldMorphism X Y) :
    f.map_structure := f.map_structure_proved

theorem finite_etale_spec (f : SourceOrbicurveCrossFieldMorphism X Y) :
    f.finite_etale := f.finite_etale_proved

end SourceOrbicurveCrossFieldMorphism

structure SourceOrbicurveSquare
    {F : Type u} [Field F]
    {X₁ Y₁ X₂ Y₂ : SourceOrbicurveObject F} where
  top : SourceOrbicurveMorphism X₁ Y₁
  bottom : SourceOrbicurveMorphism X₂ Y₂
  left : SourceOrbicurveMorphism X₁ X₂
  right : SourceOrbicurveMorphism Y₁ Y₂
  commutes : ∀ x, right.map (top.map x) = bottom.map (left.map x)
  cartesian : Prop
  cartesian_proved : cartesian

namespace SourceOrbicurveSquare

variable {F : Type u} [Field F]
variable {X₁ Y₁ X₂ Y₂ : SourceOrbicurveObject F}
variable (S : SourceOrbicurveSquare
  (X₁ := X₁) (Y₁ := Y₁) (X₂ := X₂) (Y₂ := Y₂))

theorem commutes_spec (x : X₁.carrier) :
    S.right.map (S.top.map x) = S.bottom.map (S.left.map x) :=
  S.commutes x

theorem cartesian_spec : S.cartesian := S.cartesian_proved

end SourceOrbicurveSquare

structure ClauseD (l : PrimeGeFive)
    (D : SourceInitialThetaCandidate l) where
  xF_type : D.xF.signature = SourceOrbicurveSignature.typeOneOne
  cF_type : D.cF.signature = SourceOrbicurveSignature.typeOneOne
  xK_type : D.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l
  cK_type : D.cK.signature =
    SourceOrbicurveSignature.typeOneLTorsionPlusMinus l
  signInvolution : SourceOrbicurveMorphism D.xF D.xF
  signInvolution_squared : Prop
  signInvolution_squared_proved : signInvolution_squared
  signQuotient : SourceOrbicurveMorphism D.xF D.cF
  signQuotient_invariant : Prop
  signQuotient_invariant_proved : signQuotient_invariant
  xK_to_xF : SourceOrbicurveCrossFieldMorphism D.xK D.xF
  cK_to_cF : SourceOrbicurveCrossFieldMorphism D.cK D.cF
  xK_cK_cover : SourceOrbicurveMorphism D.xK D.cK
  xK_cK_cover_finite_etale :
    xK_cK_cover.finite_etale
  xK_cK_cartesian_square :
    Prop
  xK_cK_cartesian_square_proved : xK_cK_cartesian_square
  cK_determines_xK :
    ∀ Y : SourceOrbicurveObject D.arithmetic.K,
      Y.signature = SourceOrbicurveSignature.typeOneLTorsion l →
      Nonempty (Y.carrier ≃ D.xK.carrier)
  xF_exact_sequence : SourceProfiniteExactSequence
  cF_exact_sequence : SourceProfiniteExactSequence
  xK_exact_sequence : SourceProfiniteExactSequence
  cK_exact_sequence : SourceProfiniteExactSequence
  xF_cF_group_inclusion :
    SourceExactSequenceEmbedding xF_exact_sequence cF_exact_sequence
  xK_xF_group_inclusion :
    SourceExactSequenceEmbedding xK_exact_sequence xF_exact_sequence
  cK_cF_group_inclusion :
    SourceExactSequenceEmbedding cK_exact_sequence cF_exact_sequence
  delta_x_open_subgroup : Prop
  delta_x_open_subgroup_proved : delta_x_open_subgroup
  delta_c_open_subgroup : Prop
  delta_c_open_subgroup_proved : delta_c_open_subgroup
  group_diagram_naturality : Prop
  group_diagram_naturality_proved : group_diagram_naturality

namespace ClauseD

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l} (C : ClauseD l D)
include C

theorem xF_type_spec :
    D.xF.signature = SourceOrbicurveSignature.typeOneOne := C.xF_type

theorem cF_type_spec :
    D.cF.signature = SourceOrbicurveSignature.typeOneOne := C.cF_type

theorem xK_type_spec :
    D.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l := C.xK_type

theorem cK_type_spec :
    D.cK.signature = SourceOrbicurveSignature.typeOneLTorsionPlusMinus l :=
  C.cK_type

theorem signInvolution_squared_spec : C.signInvolution_squared :=
  C.signInvolution_squared_proved

theorem signQuotient_invariant_spec : C.signQuotient_invariant :=
  C.signQuotient_invariant_proved

theorem xK_cK_cover_finite_etale_spec : C.xK_cK_cover.finite_etale :=
  C.xK_cK_cover_finite_etale

theorem xK_cK_cartesian_square_spec : C.xK_cK_cartesian_square :=
  C.xK_cK_cartesian_square_proved

theorem cK_determines_xK_spec
    (Y : SourceOrbicurveObject D.arithmetic.K)
    (hY : Y.signature = SourceOrbicurveSignature.typeOneLTorsion l) :
    Nonempty (Y.carrier ≃ D.xK.carrier) :=
  C.cK_determines_xK Y hY

theorem xF_group_inclusion_geometric_injective :
    Function.Injective C.xF_cF_group_inclusion.geometric.map :=
  C.xF_cF_group_inclusion.geometric_injective

theorem xF_group_inclusion_arithmetic_injective :
    Function.Injective C.xF_cF_group_inclusion.arithmetic.map :=
  C.xF_cF_group_inclusion.arithmetic_injective

theorem xK_group_inclusion_geometric_injective :
    Function.Injective C.xK_xF_group_inclusion.geometric.map :=
  C.xK_xF_group_inclusion.geometric_injective

theorem cK_group_inclusion_geometric_injective :
    Function.Injective C.cK_cF_group_inclusion.geometric.map :=
  C.cK_cF_group_inclusion.geometric_injective

def xF_exact_sequence_spec : SourceProfiniteExactSequence :=
  C.xF_exact_sequence

def cF_exact_sequence_spec : SourceProfiniteExactSequence :=
  C.cF_exact_sequence

def xK_exact_sequence_spec : SourceProfiniteExactSequence :=
  C.xK_exact_sequence

def cK_exact_sequence_spec : SourceProfiniteExactSequence :=
  C.cK_exact_sequence

def xF_cF_group_inclusion_spec :
    SourceExactSequenceEmbedding C.xF_exact_sequence C.cF_exact_sequence :=
  C.xF_cF_group_inclusion

def xK_xF_group_inclusion_spec :
    SourceExactSequenceEmbedding C.xK_exact_sequence C.xF_exact_sequence :=
  C.xK_xF_group_inclusion

def cK_cF_group_inclusion_spec :
    SourceExactSequenceEmbedding C.cK_exact_sequence C.cF_exact_sequence :=
  C.cK_cF_group_inclusion

theorem xF_exact_section_right_inverse
    (x : C.xF_exact_sequence.galois.carrier) :
    C.xF_exact_sequence.projection.map
      (C.xF_exact_sequence.sectionMap.map x) = x :=
  C.xF_exact_sequence.section_right_inverse x

theorem cF_exact_section_right_inverse
    (x : C.cF_exact_sequence.galois.carrier) :
    C.cF_exact_sequence.projection.map
      (C.cF_exact_sequence.sectionMap.map x) = x :=
  C.cF_exact_sequence.section_right_inverse x

theorem xK_exact_section_right_inverse
    (x : C.xK_exact_sequence.galois.carrier) :
    C.xK_exact_sequence.projection.map
      (C.xK_exact_sequence.sectionMap.map x) = x :=
  C.xK_exact_sequence.section_right_inverse x

theorem cK_exact_section_right_inverse
    (x : C.cK_exact_sequence.galois.carrier) :
    C.cK_exact_sequence.projection.map
      (C.cK_exact_sequence.sectionMap.map x) = x :=
  C.cK_exact_sequence.section_right_inverse x

theorem delta_x_open_subgroup_spec : C.delta_x_open_subgroup :=
  C.delta_x_open_subgroup_proved

theorem delta_c_open_subgroup_spec : C.delta_c_open_subgroup :=
  C.delta_c_open_subgroup_proved

theorem group_diagram_naturality_spec : C.group_diagram_naturality :=
  C.group_diagram_naturality_proved

theorem xF_exact_projection_surjective :
    Function.Surjective C.xF_exact_sequence.projection.map :=
  C.xF_exact_sequence.projection_surjective

theorem cF_exact_projection_surjective :
    Function.Surjective C.cF_exact_sequence.projection.map :=
  C.cF_exact_sequence.projection_surjective

theorem xK_exact_projection_surjective :
    Function.Surjective C.xK_exact_sequence.projection.map :=
  C.xK_exact_sequence.projection_surjective

theorem cK_exact_projection_surjective :
    Function.Surjective C.cK_exact_sequence.projection.map :=
  C.cK_exact_sequence.projection_surjective

theorem xF_exact_injection_injective :
    Function.Injective C.xF_exact_sequence.injection.map :=
  C.xF_exact_sequence.injection_injective

theorem cF_exact_injection_injective :
    Function.Injective C.cF_exact_sequence.injection.map :=
  C.cF_exact_sequence.injection_injective

theorem xK_exact_injection_injective :
    Function.Injective C.xK_exact_sequence.injection.map :=
  C.xK_exact_sequence.injection_injective

theorem cK_exact_injection_injective :
    Function.Injective C.cK_exact_sequence.injection.map :=
  C.cK_exact_sequence.injection_injective

theorem source_d_clause_bundle :
    D.xF.signature = SourceOrbicurveSignature.typeOneOne ∧
      D.cF.signature = SourceOrbicurveSignature.typeOneOne ∧
      D.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l ∧
      D.cK.signature = SourceOrbicurveSignature.typeOneLTorsionPlusMinus l ∧
      C.signInvolution_squared ∧ C.signQuotient_invariant ∧
      C.xK_cK_cartesian_square ∧ C.delta_x_open_subgroup ∧
      C.delta_c_open_subgroup := by
  exact ⟨C.xF_type, C.cF_type, C.xK_type, C.cK_type,
    C.signInvolution_squared_proved, C.signQuotient_invariant_proved,
    C.xK_cK_cartesian_square_proved,
    C.delta_x_open_subgroup_proved, C.delta_c_open_subgroup_proved⟩

theorem exact_sequence_bundle :
    Function.Surjective C.xF_exact_sequence.projection.map ∧
      Function.Injective C.xF_exact_sequence.injection.map ∧
      Function.Surjective C.cF_exact_sequence.projection.map ∧
      Function.Injective C.cF_exact_sequence.injection.map := by
  exact ⟨C.xF_exact_sequence.projection_surjective,
    C.xF_exact_sequence.injection_injective,
    C.cF_exact_sequence.projection_surjective,
    C.cF_exact_sequence.injection_injective⟩

end ClauseD

/-! ## 7. Clause (e): selected places and local fundamental-group diagrams -/

structure SourcePlacePartition (l : PrimeGeFive)
    (D : SourceInitialThetaCandidate.{u} l) where
  finiteIndex : Type u
  infiniteIndex : Type u
  finiteToV : finiteIndex → D.V
  infiniteToV : infiniteIndex → D.V
  kindPartition :
    Function.Bijective (Sum.elim finiteToV infiniteToV)
  finitePlace : finiteIndex → NumberField.FinitePlace D.arithmetic.K
  infinitePlace : infiniteIndex → NumberField.InfinitePlace D.arithmetic.K
  finite_place_compatibility : ∀ i,
    D.place (finiteToV i) = NumberFieldPlace.finite (finitePlace i)
  infinite_place_compatibility : ∀ i,
    D.place (infiniteToV i) = NumberFieldPlace.infinite (infinitePlace i)
  finite_moduli_compatibility : ∀ i,
    D.placeToMod (finiteToV i) =
      NumberFieldPlace.finite
        (NumberFieldFinitePlace.comap (finitePlace i))
  infinite_moduli_compatibility : ∀ i,
    D.placeToMod (infiniteToV i) =
      NumberFieldPlace.infinite
        ((infinitePlace i).comap
          (algebraMap D.arithmetic.Fmod D.arithmetic.K))

namespace SourcePlacePartition

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l}
variable (P : SourcePlacePartition l D)

theorem kindPartition_injective :
    Function.Injective (Sum.elim P.finiteToV P.infiniteToV) :=
  P.kindPartition.injective

theorem kindPartition_surjective :
    Function.Surjective (Sum.elim P.finiteToV P.infiniteToV) :=
  P.kindPartition.surjective

theorem finite_place_compatibility_spec (i : P.finiteIndex) :
    D.place (P.finiteToV i) = NumberFieldPlace.finite (P.finitePlace i) :=
  P.finite_place_compatibility i

theorem infinite_place_compatibility_spec (i : P.infiniteIndex) :
    D.place (P.infiniteToV i) = NumberFieldPlace.infinite (P.infinitePlace i) :=
  P.infinite_place_compatibility i

theorem finite_moduli_compatibility_spec (i : P.finiteIndex) :
    D.placeToMod (P.finiteToV i) =
      NumberFieldPlace.finite
        (NumberFieldFinitePlace.comap (P.finitePlace i)) :=
  P.finite_moduli_compatibility i

theorem infinite_moduli_compatibility_spec (i : P.infiniteIndex) :
    D.placeToMod (P.infiniteToV i) =
      NumberFieldPlace.infinite
        ((P.infinitePlace i).comap
          (algebraMap D.arithmetic.Fmod D.arithmetic.K)) :=
  P.infinite_moduli_compatibility i

theorem finite_index_lift (v : D.V)
    (h : ∃ i, P.finiteToV i = v) : Nonempty P.finiteIndex := by
  rcases h with ⟨i, hi⟩
  exact ⟨i⟩

theorem infinite_index_lift (v : D.V)
    (h : ∃ i, P.infiniteToV i = v) : Nonempty P.infiniteIndex := by
  rcases h with ⟨i, hi⟩
  exact ⟨i⟩

theorem every_selected_place_is_finite_or_infinite (v : D.V) :
    (∃ i, P.finiteToV i = v) ∨ (∃ i, P.infiniteToV i = v) := by
  rcases P.kindPartition.surjective v with ⟨s, hs⟩
  cases s with
  | inl i => exact Or.inl ⟨i, hs⟩
  | inr i => exact Or.inr ⟨i, hs⟩

theorem finite_moduli_place_is_finite (i : P.finiteIndex) :
    NumberFieldPlace.IsFinite (D.placeToMod (P.finiteToV i)) := by
  rw [P.finite_moduli_compatibility]
  trivial

theorem infinite_moduli_place_is_infinite (i : P.infiniteIndex) :
    NumberFieldPlace.IsInfinite (D.placeToMod (P.infiniteToV i)) := by
  rw [P.infinite_moduli_compatibility]
  trivial

end SourcePlacePartition

structure SourceFiniteLocalData
    (l : PrimeGeFive)
    (D : SourceInitialThetaCandidate.{u} l)
    (P : SourcePlacePartition l D)
    (i : P.finiteIndex)
    (xGlobal cGlobal : SourceProfiniteExactSequence) where
  localField : Type u
  [localField_field : Field localField]
  xLocal : SourceOrbicurveObject localField
  cLocal : SourceOrbicurveObject localField
  xLocal_signature : Prop
  xLocal_signature_proved : xLocal_signature
  cLocal_signature : Prop
  cLocal_signature_proved : cLocal_signature
  xExactSequence : SourceProfiniteExactSequence
  cExactSequence : SourceProfiniteExactSequence
  xGroupEmbedding : SourceExactSequenceEmbedding
    xExactSequence xGlobal
  cGroupEmbedding : SourceExactSequenceEmbedding
    cExactSequence cGlobal
  decompositionGroup : SourceGroup
  xLocal_decomposition_embedding : SourceGroupHom
    decompositionGroup xExactSequence.galois
  cLocal_decomposition_embedding : SourceGroupHom
    decompositionGroup cExactSequence.galois
  xLocal_decomposition_injective :
    Function.Injective xLocal_decomposition_embedding.map
  cLocal_decomposition_injective :
    Function.Injective cLocal_decomposition_embedding.map
  base_change_curve : Prop
  base_change_curve_proved : base_change_curve
  base_change_orbicurve : Prop
  base_change_orbicurve_proved : base_change_orbicurve
  local_bad_type : Prop
  local_bad_type_proved : local_bad_type
  local_q_parameter : Prop
  local_q_parameter_proved : local_q_parameter

attribute [instance] SourceFiniteLocalData.localField_field

namespace SourceFiniteLocalData

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l}
variable {P : SourcePlacePartition l D}
variable {i : P.finiteIndex}
variable {xGlobal cGlobal : SourceProfiniteExactSequence}
variable (L : SourceFiniteLocalData l D P i xGlobal cGlobal)

theorem xLocal_signature_spec : L.xLocal_signature :=
  L.xLocal_signature_proved

theorem cLocal_signature_spec : L.cLocal_signature :=
  L.cLocal_signature_proved

theorem xLocal_decomposition_injective_spec :
    Function.Injective L.xLocal_decomposition_embedding.map :=
  L.xLocal_decomposition_injective

theorem cLocal_decomposition_injective_spec :
    Function.Injective L.cLocal_decomposition_embedding.map :=
  L.cLocal_decomposition_injective

theorem base_change_curve_spec : L.base_change_curve :=
  L.base_change_curve_proved

theorem base_change_orbicurve_spec : L.base_change_orbicurve :=
  L.base_change_orbicurve_proved

theorem local_bad_type_spec : L.local_bad_type :=
  L.local_bad_type_proved

theorem local_q_parameter_spec : L.local_q_parameter :=
  L.local_q_parameter_proved

theorem local_x_projection_surjective :
    Function.Surjective L.xExactSequence.projection.map :=
  L.xExactSequence.projection_surjective

theorem local_c_projection_surjective :
    Function.Surjective L.cExactSequence.projection.map :=
  L.cExactSequence.projection_surjective

theorem local_x_injection_injective :
    Function.Injective L.xExactSequence.injection.map :=
  L.xExactSequence.injection_injective

theorem local_c_injection_injective :
    Function.Injective L.cExactSequence.injection.map :=
  L.cExactSequence.injection_injective

theorem local_exact_x (x : L.xExactSequence.arithmetic.carrier) :
    L.xExactSequence.projection.map x = 1 ↔
      ∃ y, L.xExactSequence.injection.map y = x :=
  L.xExactSequence.exact_at_arithmetic x

theorem local_exact_c (x : L.cExactSequence.arithmetic.carrier) :
    L.cExactSequence.projection.map x = 1 ↔
      ∃ y, L.cExactSequence.injection.map y = x :=
  L.cExactSequence.exact_at_arithmetic x

theorem local_section_x (x : L.xExactSequence.galois.carrier) :
    L.xExactSequence.projection.map
      (L.xExactSequence.sectionMap.map x) = x :=
  L.xExactSequence.section_right_inverse x

theorem local_section_c (x : L.cExactSequence.galois.carrier) :
    L.cExactSequence.projection.map
      (L.cExactSequence.sectionMap.map x) = x :=
  L.cExactSequence.section_right_inverse x

theorem local_clause_bundle :
    L.base_change_curve ∧ L.base_change_orbicurve ∧
      L.local_bad_type ∧ L.local_q_parameter := by
  exact ⟨L.base_change_curve_proved, L.base_change_orbicurve_proved,
    L.local_bad_type_proved, L.local_q_parameter_proved⟩

end SourceFiniteLocalData

structure SourceInfiniteLocalData
    (l : PrimeGeFive)
    (D : SourceInitialThetaCandidate.{u} l)
    (P : SourcePlacePartition l D)
    (i : P.infiniteIndex)
    (xGlobal cGlobal : SourceProfiniteExactSequence) where
  localField : Type u
  [localField_field : Field localField]
  xLocal : SourceOrbicurveObject localField
  cLocal : SourceOrbicurveObject localField
  xLocal_signature : Prop
  xLocal_signature_proved : xLocal_signature
  cLocal_signature : Prop
  cLocal_signature_proved : cLocal_signature
  xExactSequence : SourceProfiniteExactSequence
  cExactSequence : SourceProfiniteExactSequence
  xGroupEmbedding : SourceExactSequenceEmbedding
    xExactSequence xGlobal
  cGroupEmbedding : SourceExactSequenceEmbedding
    cExactSequence cGlobal
  decompositionGroup : SourceGroup
  xLocal_decomposition_embedding : SourceGroupHom
    decompositionGroup xExactSequence.galois
  cLocal_decomposition_embedding : SourceGroupHom
    decompositionGroup cExactSequence.galois
  xLocal_decomposition_injective :
    Function.Injective xLocal_decomposition_embedding.map
  cLocal_decomposition_injective :
    Function.Injective cLocal_decomposition_embedding.map
  base_change_curve : Prop
  base_change_curve_proved : base_change_curve
  base_change_orbicurve : Prop
  base_change_orbicurve_proved : base_change_orbicurve
  local_archimedean_type : Prop
  local_archimedean_type_proved : local_archimedean_type
  local_section_compatibility : Prop
  local_section_compatibility_proved : local_section_compatibility

attribute [instance] SourceInfiniteLocalData.localField_field

namespace SourceInfiniteLocalData

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l}
variable {P : SourcePlacePartition l D}
variable {i : P.infiniteIndex}
variable {xGlobal cGlobal : SourceProfiniteExactSequence}
variable (L : SourceInfiniteLocalData l D P i xGlobal cGlobal)

theorem xLocal_signature_spec : L.xLocal_signature :=
  L.xLocal_signature_proved

theorem cLocal_signature_spec : L.cLocal_signature :=
  L.cLocal_signature_proved

theorem xLocal_decomposition_injective_spec :
    Function.Injective L.xLocal_decomposition_embedding.map :=
  L.xLocal_decomposition_injective

theorem cLocal_decomposition_injective_spec :
    Function.Injective L.cLocal_decomposition_embedding.map :=
  L.cLocal_decomposition_injective

theorem base_change_curve_spec : L.base_change_curve :=
  L.base_change_curve_proved

theorem base_change_orbicurve_spec : L.base_change_orbicurve :=
  L.base_change_orbicurve_proved

theorem local_archimedean_type_spec : L.local_archimedean_type :=
  L.local_archimedean_type_proved

theorem local_section_compatibility_spec :
    L.local_section_compatibility :=
  L.local_section_compatibility_proved

theorem local_x_projection_surjective :
    Function.Surjective L.xExactSequence.projection.map :=
  L.xExactSequence.projection_surjective

theorem local_c_projection_surjective :
    Function.Surjective L.cExactSequence.projection.map :=
  L.cExactSequence.projection_surjective

theorem local_x_injection_injective :
    Function.Injective L.xExactSequence.injection.map :=
  L.xExactSequence.injection_injective

theorem local_c_injection_injective :
    Function.Injective L.cExactSequence.injection.map :=
  L.cExactSequence.injection_injective

theorem local_exact_x (x : L.xExactSequence.arithmetic.carrier) :
    L.xExactSequence.projection.map x = 1 ↔
      ∃ y, L.xExactSequence.injection.map y = x :=
  L.xExactSequence.exact_at_arithmetic x

theorem local_exact_c (x : L.cExactSequence.arithmetic.carrier) :
    L.cExactSequence.projection.map x = 1 ↔
      ∃ y, L.cExactSequence.injection.map y = x :=
  L.cExactSequence.exact_at_arithmetic x

theorem local_clause_bundle :
    L.base_change_curve ∧ L.base_change_orbicurve ∧
      L.local_archimedean_type ∧ L.local_section_compatibility := by
  exact ⟨L.base_change_curve_proved, L.base_change_orbicurve_proved,
    L.local_archimedean_type_proved,
    L.local_section_compatibility_proved⟩

end SourceInfiniteLocalData

structure ClauseE (l : PrimeGeFive)
    (D : SourceInitialThetaCandidate.{u} l)
    (C : ClauseD l D) where
  placePartition : SourcePlacePartition l D
  /- The four selected-place classes in Definition 3.1(e).  They are
     supplied as sets together with their defining predicates; a finite or
     infinite index type alone would not record the source notation
     `V^non`, `V^arc`, `V^good`, and `V^bad`. -/
  Vnon : Set D.V
  Vnon_definition : ∀ v, v ∈ Vnon ↔ NumberFieldPlace.IsFinite (D.place v)
  Varc : Set D.V
  Varc_definition : ∀ v, v ∈ Varc ↔ NumberFieldPlace.IsInfinite (D.place v)
  Vbad : Set D.V
  Vbad_definition : ∀ v,
    v ∈ Vbad ↔
      D.placeToMod v ∈ (NumberFieldPlace.finite '' D.VbadMod)
  Vgood : Set D.V
  Vgood_definition : ∀ v,
    v ∈ Vgood ↔
      D.placeToMod v ∈ D.VgoodMod
  Vnon_arc_disjoint : Disjoint Vnon Varc
  Vnon_arc_cover : Vnon ∪ Varc = Set.univ
  Vbad_good_disjoint : Disjoint Vbad Vgood
  Vbad_good_cover : Vbad ∪ Vgood = Set.univ
  V_is_section : Prop
  V_is_section_proved : V_is_section
  finiteLocal :
    ∀ i : placePartition.finiteIndex,
      SourceFiniteLocalData l D placePartition i
        C.xF_exact_sequence C.cF_exact_sequence
  infiniteLocal :
    ∀ i : placePartition.infiniteIndex,
      SourceInfiniteLocalData l D placePartition i
        C.xF_exact_sequence C.cF_exact_sequence
  finite_local_curve_diagram : Prop
  finite_local_curve_diagram_proved : finite_local_curve_diagram
  infinite_local_curve_diagram : Prop
  infinite_local_curve_diagram_proved : infinite_local_curve_diagram
  decomposition_group_naturality : Prop
  decomposition_group_naturality_proved : decomposition_group_naturality
  bad_local_orbicurve_type :
    ∀ i : placePartition.finiteIndex,
      D.placeToMod (placePartition.finiteToV i) ∈
        (NumberFieldPlace.finite '' D.VbadMod) → Prop
  bad_local_orbicurve_type_proved :
    ∀ i h,
      bad_local_orbicurve_type i h
  good_local_orbicurve_type :
    ∀ i : placePartition.finiteIndex,
      D.placeToMod (placePartition.finiteToV i) ∉
        (NumberFieldPlace.finite '' D.VbadMod) → Prop
  good_local_orbicurve_type_proved :
    ∀ i h,
      good_local_orbicurve_type i h
  local_group_projection_compatibility : Prop
  local_group_projection_compatibility_proved :
    local_group_projection_compatibility

namespace ClauseE

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l}
variable {C : ClauseD l D} (E : ClauseE l D C)
include E

def place_partition_spec : SourcePlacePartition l D :=
  E.placePartition

theorem Vnon_definition_spec (v : D.V) :
    v ∈ E.Vnon ↔ NumberFieldPlace.IsFinite (D.place v) :=
  E.Vnon_definition v

theorem Varc_definition_spec (v : D.V) :
    v ∈ E.Varc ↔ NumberFieldPlace.IsInfinite (D.place v) :=
  E.Varc_definition v

theorem Vbad_definition_spec (v : D.V) :
    v ∈ E.Vbad ↔
      D.placeToMod v ∈ (NumberFieldPlace.finite '' D.VbadMod) :=
  E.Vbad_definition v

theorem Vgood_definition_spec (v : D.V) :
    v ∈ E.Vgood ↔
      D.placeToMod v ∈ D.VgoodMod :=
  E.Vgood_definition v

theorem Vnon_arc_disjoint_spec : Disjoint E.Vnon E.Varc :=
  E.Vnon_arc_disjoint

theorem Vnon_arc_cover_spec : E.Vnon ∪ E.Varc = Set.univ :=
  E.Vnon_arc_cover

theorem Vbad_good_disjoint_spec : Disjoint E.Vbad E.Vgood :=
  E.Vbad_good_disjoint

theorem Vbad_good_cover_spec : E.Vbad ∪ E.Vgood = Set.univ :=
  E.Vbad_good_cover

theorem Vnon_or_Varc (v : D.V) : v ∈ E.Vnon ∨ v ∈ E.Varc := by
  have hv : v ∈ E.Vnon ∪ E.Varc := by
    rw [E.Vnon_arc_cover]
    exact Set.mem_univ v
  change v ∈ E.Vnon ∨ v ∈ E.Varc at hv
  exact hv

theorem Vbad_or_Vgood (v : D.V) : v ∈ E.Vbad ∨ v ∈ E.Vgood := by
  have hv : v ∈ E.Vbad ∪ E.Vgood := by
    rw [E.Vbad_good_cover]
    exact Set.mem_univ v
  change v ∈ E.Vbad ∨ v ∈ E.Vgood at hv
  exact hv

theorem not_Varc_of_mem_Vnon {v : D.V} (hv : v ∈ E.Vnon) :
    v ∉ E.Varc := by
  intro hvArc
  exact Set.disjoint_left.mp E.Vnon_arc_disjoint hv hvArc

theorem not_Vnon_of_mem_Varc {v : D.V} (hv : v ∈ E.Varc) :
    v ∉ E.Vnon := by
  intro hvNon
  exact Set.disjoint_left.mp E.Vnon_arc_disjoint hvNon hv

theorem not_Vgood_of_mem_Vbad {v : D.V} (hv : v ∈ E.Vbad) :
    v ∉ E.Vgood := by
  intro hvGood
  exact Set.disjoint_left.mp E.Vbad_good_disjoint hv hvGood

theorem not_Vbad_of_mem_Vgood {v : D.V} (hv : v ∈ E.Vgood) :
    v ∉ E.Vbad := by
  intro hvBad
  exact Set.disjoint_left.mp E.Vbad_good_disjoint hvBad hv

theorem Vnon_iff_nonarchimedean (v : D.V) :
    v ∈ E.Vnon ↔ NumberFieldPlace.IsFinite (D.place v) :=
  E.Vnon_definition v

theorem Varc_iff_archimedean (v : D.V) :
    v ∈ E.Varc ↔ NumberFieldPlace.IsInfinite (D.place v) :=
  E.Varc_definition v

theorem Vbad_iff_moduli_bad (v : D.V) :
    v ∈ E.Vbad ↔
      D.placeToMod v ∈ (NumberFieldPlace.finite '' D.VbadMod) :=
  E.Vbad_definition v

theorem Vgood_iff_moduli_good (v : D.V) :
    v ∈ E.Vgood ↔
      D.placeToMod v ∈ D.VgoodMod :=
  E.Vgood_definition v

theorem V_is_section_spec : E.V_is_section :=
  E.V_is_section_proved

theorem selected_bad_definition_spec (v : D.V) :
    v ∈ E.Vbad ↔
      D.placeToMod v ∈ (NumberFieldPlace.finite '' D.VbadMod) :=
  E.Vbad_definition v

def finiteLocal_spec (i : E.placePartition.finiteIndex) :
    SourceFiniteLocalData l D E.placePartition i
      C.xF_exact_sequence C.cF_exact_sequence :=
  E.finiteLocal i

def infiniteLocal_spec (i : E.placePartition.infiniteIndex) :
    SourceInfiniteLocalData l D E.placePartition i
      C.xF_exact_sequence C.cF_exact_sequence :=
  E.infiniteLocal i

theorem finite_local_curve_diagram_spec : E.finite_local_curve_diagram :=
  E.finite_local_curve_diagram_proved

theorem infinite_local_curve_diagram_spec :
    E.infinite_local_curve_diagram :=
  E.infinite_local_curve_diagram_proved

theorem decomposition_group_naturality_spec :
    E.decomposition_group_naturality :=
  E.decomposition_group_naturality_proved

theorem bad_local_orbicurve_type_spec
    (i : E.placePartition.finiteIndex)
    (h : D.placeToMod (E.placePartition.finiteToV i) ∈
      (NumberFieldPlace.finite '' D.VbadMod)) :
    E.bad_local_orbicurve_type i h :=
  E.bad_local_orbicurve_type_proved i h

theorem good_local_orbicurve_type_spec
    (i : E.placePartition.finiteIndex)
    (h : D.placeToMod (E.placePartition.finiteToV i) ∉
      (NumberFieldPlace.finite '' D.VbadMod)) :
    E.good_local_orbicurve_type i h :=
  E.good_local_orbicurve_type_proved i h

theorem local_group_projection_compatibility_spec :
    E.local_group_projection_compatibility :=
  E.local_group_projection_compatibility_proved

theorem finite_local_x_exact
    (i : E.placePartition.finiteIndex)
    (x : (E.finiteLocal i).xExactSequence.arithmetic.carrier) :
    (E.finiteLocal i).xExactSequence.projection.map x = 1 ↔
      ∃ y, (E.finiteLocal i).xExactSequence.injection.map y = x :=
  (E.finiteLocal i).xExactSequence.exact_at_arithmetic x

theorem finite_local_c_exact
    (i : E.placePartition.finiteIndex)
    (x : (E.finiteLocal i).cExactSequence.arithmetic.carrier) :
    (E.finiteLocal i).cExactSequence.projection.map x = 1 ↔
      ∃ y, (E.finiteLocal i).cExactSequence.injection.map y = x :=
  (E.finiteLocal i).cExactSequence.exact_at_arithmetic x

theorem infinite_local_x_exact
    (i : E.placePartition.infiniteIndex)
    (x : (E.infiniteLocal i).xExactSequence.arithmetic.carrier) :
    (E.infiniteLocal i).xExactSequence.projection.map x = 1 ↔
      ∃ y, (E.infiniteLocal i).xExactSequence.injection.map y = x :=
  (E.infiniteLocal i).xExactSequence.exact_at_arithmetic x

theorem infinite_local_c_exact
    (i : E.placePartition.infiniteIndex)
    (x : (E.infiniteLocal i).cExactSequence.arithmetic.carrier) :
    (E.infiniteLocal i).cExactSequence.projection.map x = 1 ↔
      ∃ y, (E.infiniteLocal i).cExactSequence.injection.map y = x :=
  (E.infiniteLocal i).cExactSequence.exact_at_arithmetic x

theorem source_e_clause_bundle :
    (∀ v : D.V, v ∈ E.Vnon ↔ NumberFieldPlace.IsFinite (D.place v)) ∧
      (∀ v : D.V, v ∈ E.Varc ↔ NumberFieldPlace.IsInfinite (D.place v)) ∧
      (∀ v : D.V, v ∈ E.Vbad ↔
        D.placeToMod v ∈ (NumberFieldPlace.finite '' D.VbadMod)) ∧
      (∀ v : D.V, v ∈ E.Vgood ↔
        D.placeToMod v ∈ D.VgoodMod) ∧
      Disjoint E.Vnon E.Varc ∧ E.Vnon ∪ E.Varc = Set.univ ∧
      Disjoint E.Vbad E.Vgood ∧ E.Vbad ∪ E.Vgood = Set.univ ∧
      E.V_is_section ∧ E.finite_local_curve_diagram ∧
      E.infinite_local_curve_diagram ∧
      E.decomposition_group_naturality ∧
      E.local_group_projection_compatibility := by
  exact ⟨E.Vnon_definition, E.Varc_definition,
    E.Vbad_definition, E.Vgood_definition,
    E.Vnon_arc_disjoint, E.Vnon_arc_cover,
    E.Vbad_good_disjoint, E.Vbad_good_cover,
    E.V_is_section_proved,
    E.finite_local_curve_diagram_proved,
    E.infinite_local_curve_diagram_proved,
    E.decomposition_group_naturality_proved,
    E.local_group_projection_compatibility_proved⟩

end ClauseE

/-! ## 8. Clause (f): the selected cusp and its local normalizations -/

structure SourceCuspDatum (carrier : Type u) where
  epsilon : carrier
  nonzero_quotient : Prop
  nonzero_quotient_proved : nonzero_quotient
  canonical_generator : Prop
  canonical_generator_proved : canonical_generator
  sign_ambiguity : Prop
  sign_ambiguity_proved : sign_ambiguity

namespace SourceCuspDatum

variable {carrier : Type u} (C : SourceCuspDatum carrier)

theorem nonzero_quotient_spec : C.nonzero_quotient :=
  C.nonzero_quotient_proved

theorem canonical_generator_spec : C.canonical_generator :=
  C.canonical_generator_proved

theorem sign_ambiguity_spec : C.sign_ambiguity :=
  C.sign_ambiguity_proved

theorem epsilon_eq_self : C.epsilon = C.epsilon := rfl

end SourceCuspDatum

/-!
  Definition 3.1(f) does more than choose a cusp: it constructs the two
  cusp-derived orbicurves denoted `X -> K` and `C -> K`, together with their
  finite-etale coverings and open fundamental-group inclusions.  This record
  keeps that data in the source object rather than replacing it by a single
  compatibility proposition.
-/
structure SourceCuspDerivedOrbicurves (l : PrimeGeFive)
    (D : SourceInitialThetaCandidate.{u} l)
    (C : ClauseD l D) where
  xArrow : SourceOrbicurveObject D.arithmetic.K
  cArrow : SourceOrbicurveObject D.arithmetic.K
  xArrow_signature :
    xArrow.signature = SourceOrbicurveSignature.typeOneLTorsion l
  cArrow_signature :
    cArrow.signature = SourceOrbicurveSignature.typeOneLTorsionPlusMinus l
  xArrow_to_xK : SourceOrbicurveMorphism xArrow D.xK
  cArrow_to_cK : SourceOrbicurveMorphism cArrow D.cK
  xArrow_to_cArrow : SourceOrbicurveMorphism xArrow cArrow
  xArrow_cArrow_finite_etale : xArrow_to_cArrow.finite_etale
  xArrow_exact_sequence : SourceProfiniteExactSequence
  cArrow_exact_sequence : SourceProfiniteExactSequence
  xArrow_cArrow_group_inclusion :
    SourceExactSequenceEmbedding xArrow_exact_sequence cArrow_exact_sequence
  xArrow_xK_group_inclusion :
    SourceExactSequenceEmbedding xArrow_exact_sequence C.xK_exact_sequence
  cArrow_cK_group_inclusion :
    SourceExactSequenceEmbedding cArrow_exact_sequence C.cK_exact_sequence
  xArrow_geometric_open : Prop
  xArrow_geometric_open_proved : xArrow_geometric_open
  cArrow_geometric_open : Prop
  cArrow_geometric_open_proved : cArrow_geometric_open
  xArrow_cArrow_naturality : Prop
  xArrow_cArrow_naturality_proved : xArrow_cArrow_naturality
  cusp_determines_orbicurves : Prop
  cusp_determines_orbicurves_proved : cusp_determines_orbicurves

namespace SourceCuspDerivedOrbicurves

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l}
variable {C : ClauseD l D} (A : SourceCuspDerivedOrbicurves l D C)
include A

theorem xArrow_signature_spec :
    A.xArrow.signature = SourceOrbicurveSignature.typeOneLTorsion l :=
  A.xArrow_signature

theorem cArrow_signature_spec :
    A.cArrow.signature = SourceOrbicurveSignature.typeOneLTorsionPlusMinus l :=
  A.cArrow_signature

theorem xArrow_cArrow_finite_etale_spec : A.xArrow_to_cArrow.finite_etale :=
  A.xArrow_cArrow_finite_etale

theorem xArrow_to_xK_structure_spec : A.xArrow_to_xK.map_structure :=
  A.xArrow_to_xK.map_structure_proved

theorem cArrow_to_cK_structure_spec : A.cArrow_to_cK.map_structure :=
  A.cArrow_to_cK.map_structure_proved

theorem xArrow_to_cArrow_structure_spec :
    A.xArrow_to_cArrow.map_structure :=
  A.xArrow_to_cArrow.map_structure_proved

def xArrow_exact_sequence_spec : SourceProfiniteExactSequence :=
  A.xArrow_exact_sequence

def cArrow_exact_sequence_spec : SourceProfiniteExactSequence :=
  A.cArrow_exact_sequence

def xArrow_cArrow_group_inclusion_spec :
    SourceExactSequenceEmbedding A.xArrow_exact_sequence
      A.cArrow_exact_sequence :=
  A.xArrow_cArrow_group_inclusion

def xArrow_xK_group_inclusion_spec :
    SourceExactSequenceEmbedding A.xArrow_exact_sequence C.xK_exact_sequence :=
  A.xArrow_xK_group_inclusion

def cArrow_cK_group_inclusion_spec :
    SourceExactSequenceEmbedding A.cArrow_exact_sequence C.cK_exact_sequence :=
  A.cArrow_cK_group_inclusion

theorem xArrow_geometric_open_spec : A.xArrow_geometric_open :=
  A.xArrow_geometric_open_proved

theorem cArrow_geometric_open_spec : A.cArrow_geometric_open :=
  A.cArrow_geometric_open_proved

theorem xArrow_cArrow_naturality_spec : A.xArrow_cArrow_naturality :=
  A.xArrow_cArrow_naturality_proved

theorem cusp_determines_orbicurves_spec : A.cusp_determines_orbicurves :=
  A.cusp_determines_orbicurves_proved

theorem xArrow_projection_surjective :
    Function.Surjective A.xArrow_exact_sequence.projection.map :=
  A.xArrow_exact_sequence.projection_surjective

theorem cArrow_projection_surjective :
    Function.Surjective A.cArrow_exact_sequence.projection.map :=
  A.cArrow_exact_sequence.projection_surjective

theorem xArrow_injection_injective :
    Function.Injective A.xArrow_exact_sequence.injection.map :=
  A.xArrow_exact_sequence.injection_injective

theorem cArrow_injection_injective :
    Function.Injective A.cArrow_exact_sequence.injection.map :=
  A.cArrow_exact_sequence.injection_injective

theorem xArrow_cArrow_geometric_injective :
    Function.Injective A.xArrow_cArrow_group_inclusion.geometric.map :=
  A.xArrow_cArrow_group_inclusion.geometric_injective

theorem xArrow_cArrow_arithmetic_injective :
    Function.Injective A.xArrow_cArrow_group_inclusion.arithmetic.map :=
  A.xArrow_cArrow_group_inclusion.arithmetic_injective

theorem xArrow_cArrow_galois_injective :
    Function.Injective A.xArrow_cArrow_group_inclusion.galois.map :=
  A.xArrow_cArrow_group_inclusion.galois_injective

theorem xArrow_xK_geometric_injective :
    Function.Injective A.xArrow_xK_group_inclusion.geometric.map :=
  A.xArrow_xK_group_inclusion.geometric_injective

theorem cArrow_cK_geometric_injective :
    Function.Injective A.cArrow_cK_group_inclusion.geometric.map :=
  A.cArrow_cK_group_inclusion.geometric_injective

theorem xArrow_cArrow_exact (x : A.xArrow_exact_sequence.arithmetic.carrier) :
    A.xArrow_exact_sequence.projection.map x = 1 ↔
      ∃ y, A.xArrow_exact_sequence.injection.map y = x :=
  A.xArrow_exact_sequence.exact_at_arithmetic x

theorem cArrow_cArrow_exact (x : A.cArrow_exact_sequence.arithmetic.carrier) :
    A.cArrow_exact_sequence.projection.map x = 1 ↔
      ∃ y, A.cArrow_exact_sequence.injection.map y = x :=
  A.cArrow_exact_sequence.exact_at_arithmetic x

theorem xArrow_section_right_inverse
    (x : A.xArrow_exact_sequence.galois.carrier) :
    A.xArrow_exact_sequence.projection.map
      (A.xArrow_exact_sequence.sectionMap.map x) = x :=
  A.xArrow_exact_sequence.section_right_inverse x

theorem cArrow_section_right_inverse
    (x : A.cArrow_exact_sequence.galois.carrier) :
    A.cArrow_exact_sequence.projection.map
      (A.cArrow_exact_sequence.sectionMap.map x) = x :=
  A.cArrow_exact_sequence.section_right_inverse x

theorem xArrow_cArrow_group_square
    (x : A.xArrow_exact_sequence.geometric.carrier) :
    A.xArrow_cArrow_group_inclusion.arithmetic.map
        (A.xArrow_exact_sequence.injection.map x) =
      A.cArrow_exact_sequence.injection.map
        (A.xArrow_cArrow_group_inclusion.geometric.map x) :=
  A.xArrow_cArrow_group_inclusion.inclusion_square x

theorem xArrow_cArrow_projection_square
    (x : A.xArrow_exact_sequence.arithmetic.carrier) :
    A.xArrow_cArrow_group_inclusion.galois.map
        (A.xArrow_exact_sequence.projection.map x) =
      A.cArrow_exact_sequence.projection.map
        (A.xArrow_cArrow_group_inclusion.arithmetic.map x) :=
  A.xArrow_cArrow_group_inclusion.projection_square x

theorem source_cusp_derived_bundle :
    A.xArrow.signature = SourceOrbicurveSignature.typeOneLTorsion l ∧
      A.cArrow.signature =
        SourceOrbicurveSignature.typeOneLTorsionPlusMinus l ∧
      A.xArrow_to_cArrow.finite_etale ∧
      Function.Injective A.xArrow_exact_sequence.injection.map ∧
      Function.Surjective A.xArrow_exact_sequence.projection.map ∧
      Function.Injective A.cArrow_exact_sequence.injection.map ∧
      Function.Surjective A.cArrow_exact_sequence.projection.map ∧
      A.xArrow_geometric_open ∧ A.cArrow_geometric_open ∧
      A.cusp_determines_orbicurves := by
  exact ⟨A.xArrow_signature, A.cArrow_signature,
    A.xArrow_cArrow_finite_etale,
    A.xArrow_exact_sequence.injection_injective,
    A.xArrow_exact_sequence.projection_surjective,
    A.cArrow_exact_sequence.injection_injective,
    A.cArrow_exact_sequence.projection_surjective,
    A.xArrow_geometric_open_proved, A.cArrow_geometric_open_proved,
    A.cusp_determines_orbicurves_proved⟩

end SourceCuspDerivedOrbicurves

structure ClauseF (l : PrimeGeFive)
    (D : SourceInitialThetaCandidate.{u} l)
    (C : ClauseD l D) where
  cusp : SourceCuspDatum D.epsilonCarrier
  derivedOrbicurves : SourceCuspDerivedOrbicurves l D C
  cusp_lies_on_cK : Prop
  cusp_lies_on_cK_proved : cusp_lies_on_cK
  cusp_from_nonzero_Q : Prop
  cusp_from_nonzero_Q_proved : cusp_from_nonzero_Q
  cusp_localization :
    ∀ v : D.V, Prop
  cusp_localization_proved :
    ∀ v, cusp_localization v
  bad_cusp_canonical_generator :
    ∀ (p : NumberField.FinitePlace D.arithmetic.F),
      NumberFieldFinitePlace.comap p ∈ D.VbadMod → Prop
  bad_cusp_canonical_generator_proved :
    ∀ p hp, bad_cusp_canonical_generator p hp
  good_cusp_compatibility :
    ∀ (p : NumberField.FinitePlace D.arithmetic.F),
      NumberFieldFinitePlace.comap p ∉ D.VbadMod → Prop
  good_cusp_compatibility_proved :
    ∀ p hp, good_cusp_compatibility p hp
  cusp_sign_independence : Prop
  cusp_sign_independence_proved : cusp_sign_independence
  cusp_diagram_compatibility : Prop
  cusp_diagram_compatibility_proved : cusp_diagram_compatibility

namespace ClauseF

variable {l : PrimeGeFive}
variable {D : SourceInitialThetaCandidate l}
variable {C : ClauseD l D} (F : ClauseF l D C)
include F

def cusp_spec : SourceCuspDatum D.epsilonCarrier := F.cusp

def derived_orbicurves_spec : SourceCuspDerivedOrbicurves l D C :=
  F.derivedOrbicurves

theorem derived_xArrow_signature :
    F.derivedOrbicurves.xArrow.signature =
      SourceOrbicurveSignature.typeOneLTorsion l :=
  F.derivedOrbicurves.xArrow_signature

theorem derived_cArrow_signature :
    F.derivedOrbicurves.cArrow.signature =
      SourceOrbicurveSignature.typeOneLTorsionPlusMinus l :=
  F.derivedOrbicurves.cArrow_signature

theorem derived_cover_finite_etale :
    F.derivedOrbicurves.xArrow_to_cArrow.finite_etale :=
  F.derivedOrbicurves.xArrow_cArrow_finite_etale

theorem derived_xArrow_exact
    (x : F.derivedOrbicurves.xArrow_exact_sequence.arithmetic.carrier) :
    F.derivedOrbicurves.xArrow_exact_sequence.projection.map x = 1 ↔
      ∃ y, F.derivedOrbicurves.xArrow_exact_sequence.injection.map y = x :=
  F.derivedOrbicurves.xArrow_exact_sequence.exact_at_arithmetic x

theorem derived_cArrow_exact
    (x : F.derivedOrbicurves.cArrow_exact_sequence.arithmetic.carrier) :
    F.derivedOrbicurves.cArrow_exact_sequence.projection.map x = 1 ↔
      ∃ y, F.derivedOrbicurves.cArrow_exact_sequence.injection.map y = x :=
  F.derivedOrbicurves.cArrow_exact_sequence.exact_at_arithmetic x

theorem derived_xArrow_open : F.derivedOrbicurves.xArrow_geometric_open :=
  F.derivedOrbicurves.xArrow_geometric_open_proved

theorem derived_cArrow_open : F.derivedOrbicurves.cArrow_geometric_open :=
  F.derivedOrbicurves.cArrow_geometric_open_proved

theorem derived_cusp_determines :
    F.derivedOrbicurves.cusp_determines_orbicurves :=
  F.derivedOrbicurves.cusp_determines_orbicurves_proved

theorem cusp_lies_on_cK_spec : F.cusp_lies_on_cK :=
  F.cusp_lies_on_cK_proved

theorem cusp_from_nonzero_Q_spec : F.cusp_from_nonzero_Q :=
  F.cusp_from_nonzero_Q_proved

theorem cusp_localization_spec (v : D.V) : F.cusp_localization v :=
  F.cusp_localization_proved v

theorem bad_cusp_canonical_generator_spec
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod) :
    F.bad_cusp_canonical_generator p hp :=
  F.bad_cusp_canonical_generator_proved p hp

theorem good_cusp_compatibility_spec
    (p : NumberField.FinitePlace D.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∉ D.VbadMod) :
    F.good_cusp_compatibility p hp :=
  F.good_cusp_compatibility_proved p hp

theorem cusp_sign_independence_spec : F.cusp_sign_independence :=
  F.cusp_sign_independence_proved

theorem cusp_diagram_compatibility_spec : F.cusp_diagram_compatibility :=
  F.cusp_diagram_compatibility_proved

theorem cusp_nonzero_quotient : F.cusp.nonzero_quotient :=
  F.cusp.nonzero_quotient_proved

theorem cusp_canonical_generator : F.cusp.canonical_generator :=
  F.cusp.canonical_generator_proved

theorem cusp_sign_ambiguity : F.cusp.sign_ambiguity :=
  F.cusp.sign_ambiguity_proved

theorem source_f_clause_bundle :
    F.derivedOrbicurves.xArrow.signature =
        SourceOrbicurveSignature.typeOneLTorsion l ∧
      F.derivedOrbicurves.cArrow.signature =
        SourceOrbicurveSignature.typeOneLTorsionPlusMinus l ∧
      F.derivedOrbicurves.xArrow_to_cArrow.finite_etale ∧
      F.derivedOrbicurves.cusp_determines_orbicurves ∧
      F.cusp_lies_on_cK ∧ F.cusp_from_nonzero_Q ∧
      F.cusp_sign_independence ∧ F.cusp_diagram_compatibility := by
  exact ⟨F.derivedOrbicurves.xArrow_signature,
    F.derivedOrbicurves.cArrow_signature,
    F.derivedOrbicurves.xArrow_cArrow_finite_etale,
    F.derivedOrbicurves.cusp_determines_orbicurves_proved,
    F.cusp_lies_on_cK_proved, F.cusp_from_nonzero_Q_proved,
    F.cusp_sign_independence_proved,
    F.cusp_diagram_compatibility_proved⟩

theorem cusp_localization_bundle :
    (∀ v : D.V, F.cusp_localization v) :=
  F.cusp_localization_proved

theorem bad_cusp_bundle :
    ∀ (p : NumberField.FinitePlace D.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ D.VbadMod),
      F.bad_cusp_canonical_generator p hp :=
  F.bad_cusp_canonical_generator_proved

theorem good_cusp_bundle :
    ∀ (p : NumberField.FinitePlace D.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∉ D.VbadMod),
      F.good_cusp_compatibility p hp :=
  F.good_cusp_compatibility_proved

end ClauseF

/-! ## 9. The complete source object and the general theorem -/

structure SourceInitialThetaData (l : PrimeGeFive) where
  candidate : SourceInitialThetaCandidate l
  clauseA : ClauseA l candidate
  clauseB : ClauseB l candidate
  clauseC : ClauseC l candidate
  clauseD : ClauseD l candidate
  clauseE : ClauseE l candidate clauseD
  clauseF : ClauseF l candidate clauseD
  arithmetic_clause_coherence : Prop
  arithmetic_clause_coherence_proved : arithmetic_clause_coherence
  clause_order_coherence : Prop
  clause_order_coherence_proved : clause_order_coherence

namespace SourceInitialThetaData

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

def candidate_spec : SourceInitialThetaCandidate l := S.candidate

def clauseA_spec : ClauseA l S.candidate := S.clauseA

def clauseB_spec : ClauseB l S.candidate := S.clauseB

def clauseC_spec : ClauseC l S.candidate := S.clauseC

def clauseD_spec : ClauseD l S.candidate := S.clauseD

def clauseE_spec : ClauseE l S.candidate S.clauseD := S.clauseE

def clauseF_spec : ClauseF l S.candidate S.clauseD := S.clauseF

theorem arithmetic_clause_coherence_spec : S.arithmetic_clause_coherence :=
  S.arithmetic_clause_coherence_proved

theorem clause_order_coherence_spec : S.clause_order_coherence :=
  S.clause_order_coherence_proved

theorem clause_a_square_root :
    HasSqrtNegOne S.candidate.arithmetic.F :=
  S.clauseA.squareRootNegOne

theorem clause_a_curve_signature :
    S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne :=
  S.clauseA.curve_is_once_punctured_elliptic

theorem clause_a_stable_everywhere
    (p : NumberField.FinitePlace S.candidate.arithmetic.F) :
    S.candidate.arithmetic.curve.HasStableReductionAt p :=
  S.clauseA.stable_reduction_everywhere p

theorem clause_b_bad_nonempty : S.candidate.VbadMod.Nonempty :=
  S.clauseB.bad_nonempty

theorem clause_b_bad_odd
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  S.clauseB.bad_odd_residue_characteristic p hp

theorem clause_b_stable_over_bad
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.candidate.arithmetic.curve.HasStableReductionAt p :=
  S.clauseB.stable_over_bad p hp

theorem clause_b_multiplicative_over_bad
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p :=
  S.clauseB.multiplicative_over_bad p hp

def clause_b_q_parameter
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    NumberFieldFinitePlace.FinitePlaceQCandidate p :=
  S.clauseB.qParameter p hp

theorem clause_b_q_order_prime_to_l
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    Nat.Coprime (S.clauseB.qParameter p hp).order l.value :=
  S.clauseB.q_order_prime_to_l p hp

theorem clause_c_torsion23 :
    PuncturedEllipticCurve.Torsion23Rational S.candidate.arithmetic.curve :=
  S.clauseC.torsion23_rational

theorem clause_c_image_contains_SL2 :
    S.clauseC.standard_SL2_image ≤ S.clauseC.galois_representation.range :=
  S.clauseC.image_contains_SL2

theorem clause_c_K_kernel : S.clauseC.K_kernel_field_compatibility :=
  S.clauseC.K_kernel_field_compatibility_proved

theorem clause_d_xK_type :
    S.candidate.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l :=
  S.clauseD.xK_type

theorem clause_d_cK_type :
    S.candidate.cK.signature =
      SourceOrbicurveSignature.typeOneLTorsionPlusMinus l :=
  S.clauseD.cK_type

theorem clause_d_xK_cK_cartesian : S.clauseD.xK_cK_cartesian_square :=
  S.clauseD.xK_cK_cartesian_square_proved

theorem clause_e_place_section : S.clauseE.V_is_section :=
  S.clauseE.V_is_section_proved

theorem clause_e_Vnon
    (v : S.candidate.V) :
    v ∈ S.clauseE.Vnon ↔
      NumberFieldPlace.IsFinite (S.candidate.place v) :=
  S.clauseE.Vnon_definition v

theorem clause_e_Varc
    (v : S.candidate.V) :
    v ∈ S.clauseE.Varc ↔
      NumberFieldPlace.IsInfinite (S.candidate.place v) :=
  S.clauseE.Varc_definition v

theorem clause_e_Vbad
    (v : S.candidate.V) :
    v ∈ S.clauseE.Vbad ↔
      S.candidate.placeToMod v ∈
        (NumberFieldPlace.finite '' S.candidate.VbadMod) :=
  S.clauseE.Vbad_definition v

theorem clause_e_Vgood
    (v : S.candidate.V) :
    v ∈ S.clauseE.Vgood ↔
      S.candidate.placeToMod v ∈ S.candidate.VgoodMod :=
  S.clauseE.Vgood_definition v

theorem clause_e_nonarchimedean_archimedean_partition :
    Disjoint S.clauseE.Vnon S.clauseE.Varc ∧
      S.clauseE.Vnon ∪ S.clauseE.Varc = Set.univ :=
  ⟨S.clauseE.Vnon_arc_disjoint, S.clauseE.Vnon_arc_cover⟩

theorem clause_e_good_bad_partition :
    Disjoint S.clauseE.Vbad S.clauseE.Vgood ∧
      S.clauseE.Vbad ∪ S.clauseE.Vgood = Set.univ :=
  ⟨S.clauseE.Vbad_good_disjoint, S.clauseE.Vbad_good_cover⟩

def clause_e_finite_local
    (i : S.clauseE.placePartition.finiteIndex) :
    SourceFiniteLocalData l S.candidate S.clauseE.placePartition i
      S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence :=
  S.clauseE.finiteLocal i

def clause_e_infinite_local
    (i : S.clauseE.placePartition.infiniteIndex) :
    SourceInfiniteLocalData l S.candidate S.clauseE.placePartition i
      S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence :=
  S.clauseE.infiniteLocal i

def clause_f_cusp : SourceCuspDatum S.candidate.epsilonCarrier :=
  S.clauseF.cusp

def clause_f_derived_orbicurves :
    SourceCuspDerivedOrbicurves l S.candidate S.clauseD :=
  S.clauseF.derivedOrbicurves

theorem clause_f_derived_xArrow_signature :
    S.clauseF.derivedOrbicurves.xArrow.signature =
      SourceOrbicurveSignature.typeOneLTorsion l :=
  S.clauseF.derivedOrbicurves.xArrow_signature

theorem clause_f_derived_cArrow_signature :
    S.clauseF.derivedOrbicurves.cArrow.signature =
      SourceOrbicurveSignature.typeOneLTorsionPlusMinus l :=
  S.clauseF.derivedOrbicurves.cArrow_signature

theorem clause_f_derived_cover :
    S.clauseF.derivedOrbicurves.xArrow_to_cArrow.finite_etale :=
  S.clauseF.derivedOrbicurves.xArrow_cArrow_finite_etale

theorem clause_f_cusp_nonzero : S.clauseF.cusp.nonzero_quotient :=
  S.clauseF.cusp.nonzero_quotient_proved

theorem clause_f_cusp_canonical : S.clauseF.cusp.canonical_generator :=
  S.clauseF.cusp.canonical_generator_proved

theorem clause_f_cusp_compatibility : S.clauseF.cusp_diagram_compatibility :=
  S.clauseF.cusp_diagram_compatibility_proved

structure SourceInitialThetaClauseRecords
    {l : PrimeGeFive} (S : SourceInitialThetaData l) where
  clauseA : ClauseA l S.candidate
  clauseB : ClauseB l S.candidate
  clauseC : ClauseC l S.candidate
  clauseD : ClauseD l S.candidate
  clauseE : ClauseE l S.candidate S.clauseD
  clauseF : ClauseF l S.candidate S.clauseD

def all_six_clause_records : SourceInitialThetaClauseRecords S where
  clauseA := S.clauseA
  clauseB := S.clauseB
  clauseC := S.clauseC
  clauseD := S.clauseD
  clauseE := S.clauseE
  clauseF := S.clauseF

theorem all_coherence_records :
    S.arithmetic_clause_coherence ∧ S.clause_order_coherence := by
  exact ⟨S.arithmetic_clause_coherence_proved,
    S.clause_order_coherence_proved⟩

end SourceInitialThetaData

/-!
  `InitialThetaDataConclusion` is the complete data delivered by the source
  definition.  It is deliberately universally quantified in
  `initialThetaData_conclusion`: the definition talks about every qualified
  tuple and never asserts `Nonempty (SourceInitialThetaData l)`.
-/

structure InitialThetaDataConclusion
    {l : PrimeGeFive} (S : SourceInitialThetaData l) where
  /- Retain the actual six records, not merely a conjunction of selected
     consequences.  This is the complete Definition 3.1 payload and makes
     every source field recoverable from the universal conclusion. -/
  source_clause_records : SourceInitialThetaData.SourceInitialThetaClauseRecords S
  arithmetic_clause_coherence : S.arithmetic_clause_coherence
  clause_order_coherence : S.clause_order_coherence
  clause_a_field_moduli_degree_prime_to_l :
    Nat.Coprime
      (Module.finrank S.candidate.arithmetic.Fmod S.candidate.arithmetic.F)
      l.value
  clause_a_field_moduli_galois :
    IsGalois S.candidate.arithmetic.Fmod S.candidate.arithmetic.F
  clause_a_kernel_field_galois :
    IsGalois S.candidate.arithmetic.F S.candidate.arithmetic.K
  clause_a_algebraic_closure_algebraic :
    ∀ x : AlgebraicClosure S.candidate.arithmetic.F,
      IsAlgebraic S.candidate.arithmetic.F x
  clause_a_algebraic_closure_alg_closed :
    IsAlgClosed (AlgebraicClosure S.candidate.arithmetic.F)
  clause_a_sqrtNegOne : HasSqrtNegOne S.candidate.arithmetic.F
  clause_a_algebraicClosure_field : S.clauseA.algebraicClosure_field
  clause_a_algebraicClosure_algebraic : S.clauseA.algebraicClosure_algebraic
  clause_a_curve_signature :
    S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne
  clause_a_curve_realization : S.clauseA.curve_realization
  clause_a_stable_everywhere :
    ∀ p : NumberField.FinitePlace S.candidate.arithmetic.F,
      S.candidate.arithmetic.curve.HasStableReductionAt p
  clause_a_elliptic_curve_recovery : S.clauseA.elliptic_curve_recovery
  clause_a_sign_involution_exists : S.clauseA.sign_involution_exists
  clause_a_field_of_moduli : S.clauseA.field_of_moduli
  clause_a_maximal_solvable_extension :
    IntermediateField S.candidate.arithmetic.Fmod
      (AlgebraicClosure S.candidate.arithmetic.Fmod)
  clause_a_maximal_solvable_contains :
    ∀ E : IntermediateField S.candidate.arithmetic.Fmod
      (AlgebraicClosure S.candidate.arithmetic.Fmod),
      FiniteDimensional S.candidate.arithmetic.Fmod E →
        IsGalois S.candidate.arithmetic.Fmod E →
        E ≤ clause_a_maximal_solvable_extension
  clause_a_moduli_place_definition : S.clauseA.moduli_place_definition
  clause_b_Vmod_all : S.candidate.Vmod = Set.univ
  clause_b_bad_nonempty : S.candidate.VbadMod.Nonempty
  clause_b_bad_odd :
    ∀ p : NumberField.FinitePlace S.candidate.arithmetic.Fmod,
      p ∈ S.candidate.VbadMod →
      Odd (NumberFieldFinitePlace.residueCharacteristic p)
  clause_b_bad_is_finite :
    ∀ p, p ∈ S.candidate.VbadMod →
      NumberFieldPlace.IsFinite (NumberFieldPlace.finite p)
  clause_b_bad_subset_selected :
    ∀ p, p ∈ S.candidate.VbadMod →
      NumberFieldPlace.finite p ∈ S.candidate.Vmod
  clause_b_multiplicative :
    ∀ p : NumberField.FinitePlace S.candidate.arithmetic.F,
      NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod →
      S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p
  clause_b_stable_over_bad :
    ∀ p : NumberField.FinitePlace S.candidate.arithmetic.F,
      NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod →
      S.candidate.arithmetic.curve.HasStableReductionAt p
  clause_b_q_order_prime_to_l :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
      Nat.Coprime (S.clauseB.qParameter p hp).order l.value
  clause_b_q_parameter_realizes_curve :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
      S.clauseB.q_parameter_realizes_curve p hp
  clause_b_reduction_base_change_compatibility :
    S.clauseB.reduction_base_change_compatibility
  clause_c_l_prime : Nat.Prime l.value
  clause_c_l_ge_five : 5 ≤ l.value
  clause_c_torsion23 :
    PuncturedEllipticCurve.Torsion23Rational
      S.candidate.arithmetic.curve
  clause_c_torsion_basis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      S.candidate.arithmetic.curve.LTorsion l
  clause_c_representation :
    S.clauseC.galois_representation =
      S.candidate.arithmetic.curve.galoisLTorsionMatrixRepresentation
        l S.clauseC.torsion_module_basis
  clause_c_standard_SL2_image :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))
  clause_c_standard_SL2_image_spec : S.clauseC.standard_SL2_image_spec
  clause_c_image_contains_SL2 :
    S.clauseC.standard_SL2_image ≤ S.clauseC.galois_representation.range
  clause_c_K_kernel : S.clauseC.K_kernel_field_compatibility
  clause_c_residue_prime_to_l :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := S.candidate.arithmetic.Fmod) p))
  clause_c_q_prime_to_l :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
      Nat.Coprime l.value (S.clauseC.q_order p hp)
  clause_c_q_order :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
      Nat
  clause_c_kernel_field_finite_galois : S.clauseC.kernel_field_finite_galois
  clause_c_torsion_action_continuous : S.clauseC.torsion_action_continuous
  clause_d_xF_signature :
    S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne
  clause_d_cF_signature :
    S.candidate.cF.signature = SourceOrbicurveSignature.typeOneOne
  clause_d_xK_signature :
    S.candidate.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l
  clause_d_cK_signature :
    S.candidate.cK.signature =
      SourceOrbicurveSignature.typeOneLTorsionPlusMinus l
  clause_d_sign_involution_map : SourceOrbicurveMorphism S.candidate.xF S.candidate.xF
  clause_d_sign_quotient_map : SourceOrbicurveMorphism S.candidate.xF S.candidate.cF
  clause_d_xK_to_xF :
    SourceOrbicurveCrossFieldMorphism S.candidate.xK S.candidate.xF
  clause_d_cK_to_cF :
    SourceOrbicurveCrossFieldMorphism S.candidate.cK S.candidate.cF
  clause_d_xK_cK_cover_map :
    SourceOrbicurveMorphism S.candidate.xK S.candidate.cK
  clause_d_sign_involution : S.clauseD.signInvolution_squared
  clause_d_sign_quotient : S.clauseD.signQuotient_invariant
  clause_d_cover_finite_etale : S.clauseD.xK_cK_cover.finite_etale
  clause_d_cartesian : S.clauseD.xK_cK_cartesian_square
  clause_d_cK_determines_xK :
    ∀ Y : SourceOrbicurveObject S.candidate.arithmetic.K,
      Y.signature = SourceOrbicurveSignature.typeOneLTorsion l →
      Nonempty (Y.carrier ≃ S.candidate.xK.carrier)
  clause_d_xF_exact_sequence : SourceProfiniteExactSequence
  clause_d_cF_exact_sequence : SourceProfiniteExactSequence
  clause_d_xK_exact_sequence : SourceProfiniteExactSequence
  clause_d_cK_exact_sequence : SourceProfiniteExactSequence
  clause_d_xF_cF_group_inclusion :
    SourceExactSequenceEmbedding
      clause_d_xF_exact_sequence clause_d_cF_exact_sequence
  clause_d_xK_xF_group_inclusion :
    SourceExactSequenceEmbedding
      clause_d_xK_exact_sequence clause_d_xF_exact_sequence
  clause_d_cK_cF_group_inclusion :
    SourceExactSequenceEmbedding
      clause_d_cK_exact_sequence clause_d_cF_exact_sequence
  clause_d_delta_x_open : S.clauseD.delta_x_open_subgroup
  clause_d_delta_c_open : S.clauseD.delta_c_open_subgroup
  clause_d_group_naturality : S.clauseD.group_diagram_naturality
  clause_e_section : S.clauseE.V_is_section
  clause_e_place_partition : SourcePlacePartition l S.candidate
  clause_e_Vnon : Set S.candidate.V
  clause_e_Varc : Set S.candidate.V
  clause_e_Vbad : Set S.candidate.V
  clause_e_Vgood : Set S.candidate.V
  clause_e_Vnon_definition :
    ∀ v : S.candidate.V,
      v ∈ S.clauseE.Vnon ↔
        NumberFieldPlace.IsFinite (S.candidate.place v)
  clause_e_Varc_definition :
    ∀ v : S.candidate.V,
      v ∈ S.clauseE.Varc ↔
        NumberFieldPlace.IsInfinite (S.candidate.place v)
  clause_e_Vbad_definition :
    ∀ v : S.candidate.V,
      v ∈ S.clauseE.Vbad ↔
        S.candidate.placeToMod v ∈
          (NumberFieldPlace.finite '' S.candidate.VbadMod)
  clause_e_Vgood_definition :
    ∀ v : S.candidate.V,
      v ∈ S.clauseE.Vgood ↔
        S.candidate.placeToMod v ∈
          S.candidate.VgoodMod
  clause_e_nonarchimedean_archimedean_disjoint :
    Disjoint S.clauseE.Vnon S.clauseE.Varc
  clause_e_nonarchimedean_archimedean_cover :
    S.clauseE.Vnon ∪ S.clauseE.Varc = Set.univ
  clause_e_bad_good_disjoint :
    Disjoint S.clauseE.Vbad S.clauseE.Vgood
  clause_e_bad_good_cover :
    S.clauseE.Vbad ∪ S.clauseE.Vgood = Set.univ
  clause_e_finite_local :
    ∀ i : S.clauseE.placePartition.finiteIndex,
      SourceFiniteLocalData l S.candidate S.clauseE.placePartition i
        S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence
  clause_e_infinite_local :
    ∀ i : S.clauseE.placePartition.infiniteIndex,
      SourceInfiniteLocalData l S.candidate S.clauseE.placePartition i
        S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence
  clause_e_finite_local_curve_diagram : S.clauseE.finite_local_curve_diagram
  clause_e_infinite_local_curve_diagram : S.clauseE.infinite_local_curve_diagram
  clause_e_bad_local_orbicurve_type :
    ∀ (i : S.clauseE.placePartition.finiteIndex)
      (h : S.candidate.placeToMod (S.clauseE.placePartition.finiteToV i) ∈
        (NumberFieldPlace.finite '' S.candidate.VbadMod)),
      S.clauseE.bad_local_orbicurve_type i h
  clause_e_good_local_orbicurve_type :
    ∀ (i : S.clauseE.placePartition.finiteIndex)
      (h : S.candidate.placeToMod (S.clauseE.placePartition.finiteToV i) ∉
        (NumberFieldPlace.finite '' S.candidate.VbadMod)),
      S.clauseE.good_local_orbicurve_type i h
  clause_e_decomposition_group_naturality :
    S.clauseE.decomposition_group_naturality
  clause_e_local_group_projection_compatibility :
    S.clauseE.local_group_projection_compatibility
  clause_f_derived_orbicurves :
    SourceCuspDerivedOrbicurves l S.candidate S.clauseD
  clause_f_cusp : SourceCuspDatum S.candidate.epsilonCarrier
  clause_f_cusp_sign_ambiguity : S.clauseF.cusp.sign_ambiguity
  clause_f_cusp_lies_on_cK : S.clauseF.cusp_lies_on_cK
  clause_f_cusp_from_nonzero_Q : S.clauseF.cusp_from_nonzero_Q
  clause_f_cusp_localization :
    ∀ v : S.candidate.V, S.clauseF.cusp_localization v
  clause_f_bad_cusp_canonical_generator :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
      S.clauseF.bad_cusp_canonical_generator p hp
  clause_f_good_cusp_compatibility :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∉ S.candidate.VbadMod),
      S.clauseF.good_cusp_compatibility p hp
  clause_f_cusp_sign_independence : S.clauseF.cusp_sign_independence
  clause_f_cusp_nonzero : S.clauseF.cusp.nonzero_quotient
  clause_f_cusp_canonical : S.clauseF.cusp.canonical_generator
  clause_f_cusp_compatibility : S.clauseF.cusp_diagram_compatibility

namespace InitialThetaDataConclusion

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

def source_clause_records_spec
    (C : InitialThetaDataConclusion S) :
    SourceInitialThetaData.SourceInitialThetaClauseRecords S :=
  C.source_clause_records

theorem arithmetic_clause_coherence_spec
    (C : InitialThetaDataConclusion S) : S.arithmetic_clause_coherence :=
  C.arithmetic_clause_coherence

theorem clause_order_coherence_spec
    (C : InitialThetaDataConclusion S) : S.clause_order_coherence :=
  C.clause_order_coherence

theorem clause_a_field_moduli_degree_prime_to_l_spec
    (C : InitialThetaDataConclusion S) :
    Nat.Coprime
      (Module.finrank S.candidate.arithmetic.Fmod S.candidate.arithmetic.F)
      l.value :=
  C.clause_a_field_moduli_degree_prime_to_l

theorem clause_a_field_moduli_galois_spec
    (C : InitialThetaDataConclusion S) :
    IsGalois S.candidate.arithmetic.Fmod S.candidate.arithmetic.F :=
  C.clause_a_field_moduli_galois

theorem clause_a_kernel_field_galois_spec
    (C : InitialThetaDataConclusion S) :
    IsGalois S.candidate.arithmetic.F S.candidate.arithmetic.K :=
  C.clause_a_kernel_field_galois

theorem clause_a_algebraic_closure_algebraic_spec
    (C : InitialThetaDataConclusion S)
    (x : AlgebraicClosure S.candidate.arithmetic.F) :
    IsAlgebraic S.candidate.arithmetic.F x :=
  C.clause_a_algebraic_closure_algebraic x

theorem clause_a_algebraic_closure_alg_closed_spec
    (C : InitialThetaDataConclusion S) :
    IsAlgClosed (AlgebraicClosure S.candidate.arithmetic.F) :=
  C.clause_a_algebraic_closure_alg_closed

theorem clause_a_sqrtNegOne_spec
    (C : InitialThetaDataConclusion S) :
    HasSqrtNegOne S.candidate.arithmetic.F :=
  C.clause_a_sqrtNegOne

theorem clause_a_algebraicClosure_field_spec
    (C : InitialThetaDataConclusion S) : S.clauseA.algebraicClosure_field :=
  C.clause_a_algebraicClosure_field

theorem clause_a_algebraicClosure_algebraic_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseA.algebraicClosure_algebraic :=
  C.clause_a_algebraicClosure_algebraic

theorem clause_a_curve_realization_spec
    (C : InitialThetaDataConclusion S) : S.clauseA.curve_realization :=
  C.clause_a_curve_realization

theorem clause_a_elliptic_curve_recovery_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseA.elliptic_curve_recovery :=
  C.clause_a_elliptic_curve_recovery

theorem clause_a_sign_involution_exists_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseA.sign_involution_exists :=
  C.clause_a_sign_involution_exists

theorem clause_a_field_of_moduli_spec
    (C : InitialThetaDataConclusion S) : S.clauseA.field_of_moduli :=
  C.clause_a_field_of_moduli

def clause_a_maximal_solvable_extension_spec
    (C : InitialThetaDataConclusion S) :
    IntermediateField S.candidate.arithmetic.Fmod
      (AlgebraicClosure S.candidate.arithmetic.Fmod) :=
  C.clause_a_maximal_solvable_extension

theorem clause_a_maximal_solvable_contains_spec
    (C : InitialThetaDataConclusion S)
    (E : IntermediateField S.candidate.arithmetic.Fmod
      (AlgebraicClosure S.candidate.arithmetic.Fmod))
    (hfinite : FiniteDimensional S.candidate.arithmetic.Fmod E)
    (hgalois : IsGalois S.candidate.arithmetic.Fmod E) :
    E ≤ C.clause_a_maximal_solvable_extension :=
  C.clause_a_maximal_solvable_contains E hfinite hgalois

theorem clause_a_moduli_place_definition_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseA.moduli_place_definition :=
  C.clause_a_moduli_place_definition

theorem clause_a_curve_signature_spec
    (C : InitialThetaDataConclusion S) :
    S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne :=
  C.clause_a_curve_signature

theorem clause_a_stable_everywhere_spec
    (C : InitialThetaDataConclusion S)
    (p : NumberField.FinitePlace S.candidate.arithmetic.F) :
    S.candidate.arithmetic.curve.HasStableReductionAt p :=
  C.clause_a_stable_everywhere p

theorem clause_b_bad_nonempty_spec
    (C : InitialThetaDataConclusion S) : S.candidate.VbadMod.Nonempty :=
  C.clause_b_bad_nonempty

theorem clause_b_Vmod_all_spec
    (C : InitialThetaDataConclusion S) : S.candidate.Vmod = Set.univ :=
  C.clause_b_Vmod_all

theorem clause_b_bad_odd_spec
    (C : InitialThetaDataConclusion S)
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  C.clause_b_bad_odd p hp

theorem clause_b_bad_is_finite_spec
    (C : InitialThetaDataConclusion S)
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.IsFinite (NumberFieldPlace.finite p) :=
  C.clause_b_bad_is_finite p hp

theorem clause_b_bad_subset_selected_spec
    (C : InitialThetaDataConclusion S)
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.finite p ∈ S.candidate.Vmod :=
  C.clause_b_bad_subset_selected p hp

theorem clause_b_multiplicative_spec
    (C : InitialThetaDataConclusion S)
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p :=
  C.clause_b_multiplicative p hp

theorem clause_b_stable_over_bad_spec
    (C : InitialThetaDataConclusion S)
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.candidate.arithmetic.curve.HasStableReductionAt p :=
  C.clause_b_stable_over_bad p hp

theorem clause_b_q_order_spec
    (C : InitialThetaDataConclusion S)
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    Nat.Coprime (S.clauseB.qParameter p hp).order l.value :=
  C.clause_b_q_order_prime_to_l p hp

theorem clause_b_q_parameter_realizes_curve_spec
    (C : InitialThetaDataConclusion S)
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.clauseB.q_parameter_realizes_curve p hp :=
  C.clause_b_q_parameter_realizes_curve p hp

theorem clause_b_reduction_base_change_compatibility_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseB.reduction_base_change_compatibility :=
  C.clause_b_reduction_base_change_compatibility

theorem clause_c_torsion23_spec
    (C : InitialThetaDataConclusion S) :
    PuncturedEllipticCurve.Torsion23Rational
      S.candidate.arithmetic.curve :=
  C.clause_c_torsion23

theorem clause_c_l_prime_spec
    (C : InitialThetaDataConclusion S) : Nat.Prime l.value :=
  C.clause_c_l_prime

theorem clause_c_l_ge_five_spec
    (C : InitialThetaDataConclusion S) : 5 ≤ l.value :=
  C.clause_c_l_ge_five

def clause_c_torsion_basis_spec
    (C : InitialThetaDataConclusion S) :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      S.candidate.arithmetic.curve.LTorsion l :=
  C.clause_c_torsion_basis

theorem clause_c_representation_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseC.galois_representation =
      S.candidate.arithmetic.curve.galoisLTorsionMatrixRepresentation
        l S.clauseC.torsion_module_basis :=
  C.clause_c_representation

def clause_c_standard_SL2_image_value_spec
    (C : InitialThetaDataConclusion S) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) :=
  C.clause_c_standard_SL2_image

theorem clause_c_standard_SL2_image_property_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseC.standard_SL2_image_spec :=
  C.clause_c_standard_SL2_image_spec

theorem clause_c_image_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseC.standard_SL2_image ≤ S.clauseC.galois_representation.range :=
  C.clause_c_image_contains_SL2

theorem clause_c_K_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseC.K_kernel_field_compatibility :=
  C.clause_c_K_kernel

theorem clause_c_residue_prime_to_l_spec
    (C : InitialThetaDataConclusion S)
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
      Nat.Coprime l.value
      (NumberFieldFinitePlace.residueCharacteristic
        (NumberFieldFinitePlace.comap (k := S.candidate.arithmetic.Fmod) p)) :=
  C.clause_c_residue_prime_to_l p hp

theorem clause_c_q_prime_to_l_spec
    (C : InitialThetaDataConclusion S)
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    Nat.Coprime l.value (S.clauseC.q_order p hp) :=
  C.clause_c_q_prime_to_l p hp

def clause_c_q_order_spec
    (C : InitialThetaDataConclusion S)
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    Nat :=
  C.clause_c_q_order p hp

theorem clause_c_kernel_field_finite_galois_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseC.kernel_field_finite_galois :=
  C.clause_c_kernel_field_finite_galois

theorem clause_c_torsion_action_continuous_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseC.torsion_action_continuous :=
  C.clause_c_torsion_action_continuous

theorem clause_d_xK_spec
    (C : InitialThetaDataConclusion S) :
    S.candidate.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l :=
  C.clause_d_xK_signature

theorem clause_d_xF_spec
    (C : InitialThetaDataConclusion S) :
    S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne :=
  C.clause_d_xF_signature

theorem clause_d_cF_spec
    (C : InitialThetaDataConclusion S) :
    S.candidate.cF.signature = SourceOrbicurveSignature.typeOneOne :=
  C.clause_d_cF_signature

theorem clause_d_cK_spec
    (C : InitialThetaDataConclusion S) :
    S.candidate.cK.signature =
      SourceOrbicurveSignature.typeOneLTorsionPlusMinus l :=
  C.clause_d_cK_signature

theorem clause_d_cartesian_spec
    (C : InitialThetaDataConclusion S) : S.clauseD.xK_cK_cartesian_square :=
  C.clause_d_cartesian

theorem clause_d_sign_involution_spec
    (C : InitialThetaDataConclusion S) : S.clauseD.signInvolution_squared :=
  C.clause_d_sign_involution

theorem clause_d_sign_quotient_spec
    (C : InitialThetaDataConclusion S) : S.clauseD.signQuotient_invariant :=
  C.clause_d_sign_quotient

theorem clause_d_cover_finite_etale_spec
    (C : InitialThetaDataConclusion S) : S.clauseD.xK_cK_cover.finite_etale :=
  C.clause_d_cover_finite_etale

theorem clause_d_delta_x_open_spec
    (C : InitialThetaDataConclusion S) : S.clauseD.delta_x_open_subgroup :=
  C.clause_d_delta_x_open

theorem clause_d_delta_c_open_spec
    (C : InitialThetaDataConclusion S) : S.clauseD.delta_c_open_subgroup :=
  C.clause_d_delta_c_open

theorem clause_d_group_naturality_spec
    (C : InitialThetaDataConclusion S) : S.clauseD.group_diagram_naturality :=
  C.clause_d_group_naturality

def clause_d_sign_involution_map_spec
    (C : InitialThetaDataConclusion S) :
    SourceOrbicurveMorphism S.candidate.xF S.candidate.xF :=
  C.clause_d_sign_involution_map

def clause_d_sign_quotient_map_spec
    (C : InitialThetaDataConclusion S) :
    SourceOrbicurveMorphism S.candidate.xF S.candidate.cF :=
  C.clause_d_sign_quotient_map

def clause_d_xK_to_xF_spec
    (C : InitialThetaDataConclusion S) :
    SourceOrbicurveCrossFieldMorphism S.candidate.xK S.candidate.xF :=
  C.clause_d_xK_to_xF

def clause_d_cK_to_cF_spec
    (C : InitialThetaDataConclusion S) :
    SourceOrbicurveCrossFieldMorphism S.candidate.cK S.candidate.cF :=
  C.clause_d_cK_to_cF

def clause_d_xK_cK_cover_map_spec
    (C : InitialThetaDataConclusion S) :
    SourceOrbicurveMorphism S.candidate.xK S.candidate.cK :=
  C.clause_d_xK_cK_cover_map

theorem clause_d_cK_determines_xK_spec
    (C : InitialThetaDataConclusion S)
    (Y : SourceOrbicurveObject S.candidate.arithmetic.K)
    (hY : Y.signature = SourceOrbicurveSignature.typeOneLTorsion l) :
    Nonempty (Y.carrier ≃ S.candidate.xK.carrier) :=
  C.clause_d_cK_determines_xK Y hY

def clause_d_xF_exact_sequence_spec
    (C : InitialThetaDataConclusion S) : SourceProfiniteExactSequence :=
  C.clause_d_xF_exact_sequence

def clause_d_cF_exact_sequence_spec
    (C : InitialThetaDataConclusion S) : SourceProfiniteExactSequence :=
  C.clause_d_cF_exact_sequence

def clause_d_xK_exact_sequence_spec
    (C : InitialThetaDataConclusion S) : SourceProfiniteExactSequence :=
  C.clause_d_xK_exact_sequence

def clause_d_cK_exact_sequence_spec
    (C : InitialThetaDataConclusion S) : SourceProfiniteExactSequence :=
  C.clause_d_cK_exact_sequence

def clause_d_xF_cF_group_inclusion_spec
    (C : InitialThetaDataConclusion S) :
    SourceExactSequenceEmbedding
      C.clause_d_xF_exact_sequence C.clause_d_cF_exact_sequence :=
  C.clause_d_xF_cF_group_inclusion

def clause_d_xK_xF_group_inclusion_spec
    (C : InitialThetaDataConclusion S) :
    SourceExactSequenceEmbedding
      C.clause_d_xK_exact_sequence C.clause_d_xF_exact_sequence :=
  C.clause_d_xK_xF_group_inclusion

def clause_d_cK_cF_group_inclusion_spec
    (C : InitialThetaDataConclusion S) :
    SourceExactSequenceEmbedding
      C.clause_d_cK_exact_sequence C.clause_d_cF_exact_sequence :=
  C.clause_d_cK_cF_group_inclusion

theorem clause_e_section_spec
    (C : InitialThetaDataConclusion S) : S.clauseE.V_is_section :=
  C.clause_e_section

def clause_e_place_partition_spec
    (C : InitialThetaDataConclusion S) : SourcePlacePartition l S.candidate :=
  C.clause_e_place_partition

def clause_e_Vnon_spec_set
    (C : InitialThetaDataConclusion S) : Set S.candidate.V :=
  C.clause_e_Vnon

def clause_e_Varc_spec_set
    (C : InitialThetaDataConclusion S) : Set S.candidate.V :=
  C.clause_e_Varc

def clause_e_Vbad_spec_set
    (C : InitialThetaDataConclusion S) : Set S.candidate.V :=
  C.clause_e_Vbad

def clause_e_Vgood_spec_set
    (C : InitialThetaDataConclusion S) : Set S.candidate.V :=
  C.clause_e_Vgood

theorem clause_e_Vnon_definition_spec
    (C : InitialThetaDataConclusion S) (v : S.candidate.V) :
    v ∈ S.clauseE.Vnon ↔
      NumberFieldPlace.IsFinite (S.candidate.place v) :=
  C.clause_e_Vnon_definition v

theorem clause_e_Varc_definition_spec
    (C : InitialThetaDataConclusion S) (v : S.candidate.V) :
    v ∈ S.clauseE.Varc ↔
      NumberFieldPlace.IsInfinite (S.candidate.place v) :=
  C.clause_e_Varc_definition v

theorem clause_e_Vbad_definition_spec
    (C : InitialThetaDataConclusion S) (v : S.candidate.V) :
    v ∈ S.clauseE.Vbad ↔
      S.candidate.placeToMod v ∈
        (NumberFieldPlace.finite '' S.candidate.VbadMod) :=
  C.clause_e_Vbad_definition v

theorem clause_e_Vgood_definition_spec
    (C : InitialThetaDataConclusion S) (v : S.candidate.V) :
    v ∈ S.clauseE.Vgood ↔
      S.candidate.placeToMod v ∈
        S.candidate.VgoodMod :=
  C.clause_e_Vgood_definition v

theorem clause_e_nonarchimedean_archimedean_disjoint_spec
    (C : InitialThetaDataConclusion S) :
    Disjoint S.clauseE.Vnon S.clauseE.Varc :=
  C.clause_e_nonarchimedean_archimedean_disjoint

theorem clause_e_nonarchimedean_archimedean_cover_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseE.Vnon ∪ S.clauseE.Varc = Set.univ :=
  C.clause_e_nonarchimedean_archimedean_cover

theorem clause_e_bad_good_disjoint_spec
    (C : InitialThetaDataConclusion S) :
    Disjoint S.clauseE.Vbad S.clauseE.Vgood :=
  C.clause_e_bad_good_disjoint

theorem clause_e_bad_good_cover_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseE.Vbad ∪ S.clauseE.Vgood = Set.univ :=
  C.clause_e_bad_good_cover

def clause_e_finite_local_spec
    (C : InitialThetaDataConclusion S)
    (i : S.clauseE.placePartition.finiteIndex) :
    SourceFiniteLocalData l S.candidate S.clauseE.placePartition i
      S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence :=
  C.clause_e_finite_local i

def clause_e_infinite_local_spec
    (C : InitialThetaDataConclusion S)
    (i : S.clauseE.placePartition.infiniteIndex) :
    SourceInfiniteLocalData l S.candidate S.clauseE.placePartition i
      S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence :=
  C.clause_e_infinite_local i

theorem clause_e_finite_local_curve_diagram_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseE.finite_local_curve_diagram :=
  C.clause_e_finite_local_curve_diagram

theorem clause_e_infinite_local_curve_diagram_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseE.infinite_local_curve_diagram :=
  C.clause_e_infinite_local_curve_diagram

theorem clause_e_bad_local_orbicurve_type_spec
    (C : InitialThetaDataConclusion S)
    (i : S.clauseE.placePartition.finiteIndex)
    (h : S.candidate.placeToMod (S.clauseE.placePartition.finiteToV i) ∈
      (NumberFieldPlace.finite '' S.candidate.VbadMod)) :
    S.clauseE.bad_local_orbicurve_type i h :=
  C.clause_e_bad_local_orbicurve_type i h

theorem clause_e_good_local_orbicurve_type_spec
    (C : InitialThetaDataConclusion S)
    (i : S.clauseE.placePartition.finiteIndex)
    (h : S.candidate.placeToMod (S.clauseE.placePartition.finiteToV i) ∉
      (NumberFieldPlace.finite '' S.candidate.VbadMod)) :
    S.clauseE.good_local_orbicurve_type i h :=
  C.clause_e_good_local_orbicurve_type i h

theorem clause_e_decomposition_group_naturality_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseE.decomposition_group_naturality :=
  C.clause_e_decomposition_group_naturality

theorem clause_e_local_group_projection_compatibility_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseE.local_group_projection_compatibility :=
  C.clause_e_local_group_projection_compatibility

theorem clause_f_cusp_nonzero_spec
    (C : InitialThetaDataConclusion S) : S.clauseF.cusp.nonzero_quotient :=
  C.clause_f_cusp_nonzero

def clause_f_derived_orbicurves_spec
    (C : InitialThetaDataConclusion S) :
    SourceCuspDerivedOrbicurves l S.candidate S.clauseD :=
  C.clause_f_derived_orbicurves

def clause_f_cusp_spec
    (C : InitialThetaDataConclusion S) :
    SourceCuspDatum S.candidate.epsilonCarrier :=
  C.clause_f_cusp

theorem clause_f_cusp_sign_ambiguity_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseF.cusp.sign_ambiguity :=
  C.clause_f_cusp_sign_ambiguity

theorem clause_f_cusp_lies_on_cK_spec
    (C : InitialThetaDataConclusion S) : S.clauseF.cusp_lies_on_cK :=
  C.clause_f_cusp_lies_on_cK

theorem clause_f_cusp_from_nonzero_Q_spec
    (C : InitialThetaDataConclusion S) : S.clauseF.cusp_from_nonzero_Q :=
  C.clause_f_cusp_from_nonzero_Q

theorem clause_f_cusp_localization_spec
    (C : InitialThetaDataConclusion S) (v : S.candidate.V) :
    S.clauseF.cusp_localization v :=
  C.clause_f_cusp_localization v

theorem clause_f_bad_cusp_canonical_generator_spec
    (C : InitialThetaDataConclusion S)
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.clauseF.bad_cusp_canonical_generator p hp :=
  C.clause_f_bad_cusp_canonical_generator p hp

theorem clause_f_good_cusp_compatibility_spec
    (C : InitialThetaDataConclusion S)
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∉ S.candidate.VbadMod) :
    S.clauseF.good_cusp_compatibility p hp :=
  C.clause_f_good_cusp_compatibility p hp

theorem clause_f_cusp_sign_independence_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseF.cusp_sign_independence :=
  C.clause_f_cusp_sign_independence

theorem clause_f_cusp_canonical_spec
    (C : InitialThetaDataConclusion S) : S.clauseF.cusp.canonical_generator :=
  C.clause_f_cusp_canonical

theorem clause_f_cusp_compatibility_spec
    (C : InitialThetaDataConclusion S) :
    S.clauseF.cusp_diagram_compatibility :=
  C.clause_f_cusp_compatibility

end InitialThetaDataConclusion

def SourceInitialThetaData.conclusion
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    InitialThetaDataConclusion S where
  source_clause_records := S.all_six_clause_records
  arithmetic_clause_coherence := S.arithmetic_clause_coherence_proved
  clause_order_coherence := S.clause_order_coherence_proved
  clause_a_field_moduli_degree_prime_to_l :=
    S.candidate.fieldModuli_degree_prime_to_l
  clause_a_field_moduli_galois := S.candidate.fieldModuli_is_galois
  clause_a_kernel_field_galois := S.candidate.fieldK_is_galois
  clause_a_algebraic_closure_algebraic :=
    S.candidate.algebraicClosure_is_algebraic
  clause_a_algebraic_closure_alg_closed :=
    S.candidate.algebraicClosure_is_alg_closed
  clause_a_sqrtNegOne := S.clauseA.squareRootNegOne
  clause_a_algebraicClosure_field := S.clauseA.algebraicClosure_field_proved
  clause_a_algebraicClosure_algebraic :=
    S.clauseA.algebraicClosure_algebraic_proved
  clause_a_curve_signature := S.clauseA.curve_is_once_punctured_elliptic
  clause_a_curve_realization := S.clauseA.curve_realization_proved
  clause_a_stable_everywhere := S.clauseA.stable_reduction_everywhere
  clause_a_elliptic_curve_recovery :=
    S.clauseA.elliptic_curve_recovery_proved
  clause_a_sign_involution_exists := S.clauseA.sign_involution_exists_proved
  clause_a_field_of_moduli := S.clauseA.field_of_moduli_proved
  clause_a_maximal_solvable_extension :=
    S.clauseA.maximal_solvable_extension
  clause_a_maximal_solvable_contains := by
    intro E hfinite hgalois
    exact S.clauseA.maximal_solvable_contains E hfinite hgalois
  clause_a_moduli_place_definition :=
    S.clauseA.moduli_place_definition_proved
  clause_b_Vmod_all := S.candidate.Vmod_eq_univ
  clause_b_bad_nonempty := S.clauseB.bad_nonempty
  clause_b_bad_odd := S.clauseB.bad_odd_residue_characteristic
  clause_b_bad_is_finite := S.clauseB.bad_is_finite
  clause_b_bad_subset_selected := S.clauseB.bad_subset_selected
  clause_b_multiplicative := S.clauseB.multiplicative_over_bad
  clause_b_stable_over_bad := S.clauseB.stable_over_bad
  clause_b_q_order_prime_to_l := S.clauseB.q_order_prime_to_l
  clause_b_q_parameter_realizes_curve :=
    S.clauseB.q_parameter_realizes_curve_proved
  clause_b_reduction_base_change_compatibility :=
    S.clauseB.reduction_base_change_compatibility_proved
  clause_c_l_prime := l.prime
  clause_c_l_ge_five := l.ge_five
  clause_c_torsion23 := S.clauseC.torsion23_rational
  clause_c_torsion_basis := S.clauseC.torsion_module_basis
  clause_c_representation := S.clauseC.galois_representation_eq_canonical
  clause_c_standard_SL2_image := S.clauseC.standard_SL2_image
  clause_c_standard_SL2_image_spec :=
    S.clauseC.standard_SL2_image_spec_proved
  clause_c_image_contains_SL2 := S.clauseC.image_contains_SL2
  clause_c_K_kernel := S.clauseC.K_kernel_field_compatibility_proved
  clause_c_residue_prime_to_l :=
    S.clauseC.l_prime_to_bad_residue_characteristics
  clause_c_q_prime_to_l := S.clauseC.l_prime_to_q_orders
  clause_c_q_order := S.clauseC.q_order
  clause_c_kernel_field_finite_galois :=
    S.clauseC.kernel_field_finite_galois_proved
  clause_c_torsion_action_continuous :=
    S.clauseC.torsion_action_continuous_proved
  clause_d_xF_signature := S.clauseD.xF_type
  clause_d_cF_signature := S.clauseD.cF_type
  clause_d_xK_signature := S.clauseD.xK_type
  clause_d_cK_signature := S.clauseD.cK_type
  clause_d_sign_involution_map := S.clauseD.signInvolution
  clause_d_sign_quotient_map := S.clauseD.signQuotient
  clause_d_xK_to_xF := S.clauseD.xK_to_xF
  clause_d_cK_to_cF := S.clauseD.cK_to_cF
  clause_d_xK_cK_cover_map := S.clauseD.xK_cK_cover
  clause_d_sign_involution := S.clauseD.signInvolution_squared_proved
  clause_d_sign_quotient := S.clauseD.signQuotient_invariant_proved
  clause_d_cover_finite_etale := S.clauseD.xK_cK_cover_finite_etale
  clause_d_cartesian := S.clauseD.xK_cK_cartesian_square_proved
  clause_d_cK_determines_xK := S.clauseD.cK_determines_xK
  clause_d_xF_exact_sequence := S.clauseD.xF_exact_sequence
  clause_d_cF_exact_sequence := S.clauseD.cF_exact_sequence
  clause_d_xK_exact_sequence := S.clauseD.xK_exact_sequence
  clause_d_cK_exact_sequence := S.clauseD.cK_exact_sequence
  clause_d_xF_cF_group_inclusion := S.clauseD.xF_cF_group_inclusion
  clause_d_xK_xF_group_inclusion := S.clauseD.xK_xF_group_inclusion
  clause_d_cK_cF_group_inclusion := S.clauseD.cK_cF_group_inclusion
  clause_d_delta_x_open := S.clauseD.delta_x_open_subgroup_proved
  clause_d_delta_c_open := S.clauseD.delta_c_open_subgroup_proved
  clause_d_group_naturality := S.clauseD.group_diagram_naturality_proved
  clause_e_section := S.clauseE.V_is_section_proved
  clause_e_place_partition := S.clauseE.placePartition
  clause_e_Vnon := S.clauseE.Vnon
  clause_e_Varc := S.clauseE.Varc
  clause_e_Vbad := S.clauseE.Vbad
  clause_e_Vgood := S.clauseE.Vgood
  clause_e_Vnon_definition := S.clauseE.Vnon_definition
  clause_e_Varc_definition := S.clauseE.Varc_definition
  clause_e_Vbad_definition := S.clauseE.Vbad_definition
  clause_e_Vgood_definition := S.clauseE.Vgood_definition
  clause_e_nonarchimedean_archimedean_disjoint :=
    S.clauseE.Vnon_arc_disjoint
  clause_e_nonarchimedean_archimedean_cover :=
    S.clauseE.Vnon_arc_cover
  clause_e_bad_good_disjoint := S.clauseE.Vbad_good_disjoint
  clause_e_bad_good_cover := S.clauseE.Vbad_good_cover
  clause_e_finite_local := S.clauseE.finiteLocal
  clause_e_infinite_local := S.clauseE.infiniteLocal
  clause_e_finite_local_curve_diagram :=
    S.clauseE.finite_local_curve_diagram_proved
  clause_e_infinite_local_curve_diagram :=
    S.clauseE.infinite_local_curve_diagram_proved
  clause_e_bad_local_orbicurve_type :=
    S.clauseE.bad_local_orbicurve_type_proved
  clause_e_good_local_orbicurve_type :=
    S.clauseE.good_local_orbicurve_type_proved
  clause_e_decomposition_group_naturality :=
    S.clauseE.decomposition_group_naturality_proved
  clause_e_local_group_projection_compatibility :=
    S.clauseE.local_group_projection_compatibility_proved
  clause_f_derived_orbicurves := S.clauseF.derivedOrbicurves
  clause_f_cusp := S.clauseF.cusp
  clause_f_cusp_sign_ambiguity := S.clauseF.cusp.sign_ambiguity_proved
  clause_f_cusp_lies_on_cK := S.clauseF.cusp_lies_on_cK_proved
  clause_f_cusp_from_nonzero_Q := S.clauseF.cusp_from_nonzero_Q_proved
  clause_f_cusp_localization := S.clauseF.cusp_localization_proved
  clause_f_bad_cusp_canonical_generator :=
    S.clauseF.bad_cusp_canonical_generator_proved
  clause_f_good_cusp_compatibility :=
    S.clauseF.good_cusp_compatibility_proved
  clause_f_cusp_sign_independence := S.clauseF.cusp_sign_independence_proved
  clause_f_cusp_nonzero := S.clauseF.cusp.nonzero_quotient_proved
  clause_f_cusp_canonical := S.clauseF.cusp.canonical_generator_proved
  clause_f_cusp_compatibility := S.clauseF.cusp_diagram_compatibility_proved

def initialThetaData_conclusion
    {l : PrimeGeFive} :
    ∀ S : SourceInitialThetaData l,
      InitialThetaDataConclusion S := by
  intro S
  exact S.conclusion

def initialThetaData_conclusion_complete
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    SourceInitialThetaData.SourceInitialThetaClauseRecords S :=
  (initialThetaData_conclusion S).source_clause_records

theorem initialThetaData_conclusion_coherence
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    S.arithmetic_clause_coherence ∧ S.clause_order_coherence :=
  ⟨(initialThetaData_conclusion S).arithmetic_clause_coherence,
    (initialThetaData_conclusion S).clause_order_coherence⟩

theorem initialThetaData_conclusion_clause_a
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    Nat.Coprime
      (Module.finrank S.candidate.arithmetic.Fmod S.candidate.arithmetic.F)
      l.value ∧
      IsGalois S.candidate.arithmetic.Fmod S.candidate.arithmetic.F ∧
      (∀ x : AlgebraicClosure S.candidate.arithmetic.F,
        IsAlgebraic S.candidate.arithmetic.F x) ∧
      IsAlgClosed (AlgebraicClosure S.candidate.arithmetic.F) ∧
      HasSqrtNegOne S.candidate.arithmetic.F ∧
      S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne ∧
      (∀ p : NumberField.FinitePlace S.candidate.arithmetic.F,
        S.candidate.arithmetic.curve.HasStableReductionAt p) := by
  exact ⟨S.candidate.fieldModuli_degree_prime_to_l,
    S.candidate.fieldModuli_is_galois,
    S.candidate.algebraicClosure_is_algebraic,
    S.candidate.algebraicClosure_is_alg_closed,
    S.clauseA.squareRootNegOne,
    S.clauseA.curve_is_once_punctured_elliptic,
    S.clauseA.stable_reduction_everywhere⟩

theorem initialThetaData_conclusion_clause_b
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    S.candidate.Vmod = Set.univ ∧ S.candidate.VbadMod.Nonempty ∧
      (∀ p, p ∈ S.candidate.VbadMod →
        Odd (NumberFieldFinitePlace.residueCharacteristic p)) ∧
      (∀ p hp, Nat.Coprime (S.clauseB.qParameter p hp).order l.value) := by
  exact ⟨S.candidate.Vmod_eq_univ, S.clauseB.bad_nonempty,
    S.clauseB.bad_odd_residue_characteristic,
    S.clauseB.q_order_prime_to_l⟩

theorem initialThetaData_conclusion_clause_c
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    Nat.Prime l.value ∧ 5 ≤ l.value ∧
      PuncturedEllipticCurve.Torsion23Rational S.candidate.arithmetic.curve ∧
      S.clauseC.galois_representation =
        S.candidate.arithmetic.curve.galoisLTorsionMatrixRepresentation
          l S.clauseC.torsion_module_basis ∧
      S.clauseC.standard_SL2_image ≤ S.clauseC.galois_representation.range ∧
      S.clauseC.K_kernel_field_compatibility ∧
      (∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
        (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
        Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := S.candidate.arithmetic.Fmod) p))) ∧
      (∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
        (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
        Nat.Coprime l.value (S.clauseC.q_order p hp)) ∧
      S.clauseC.kernel_field_finite_galois ∧
      S.clauseC.torsion_action_continuous := by
  exact ⟨l.prime, l.ge_five, S.clauseC.torsion23_rational,
    S.clauseC.galois_representation_eq_canonical,
    S.clauseC.image_contains_SL2,
    S.clauseC.K_kernel_field_compatibility_proved,
    S.clauseC.l_prime_to_bad_residue_characteristics,
    S.clauseC.l_prime_to_q_orders,
    S.clauseC.kernel_field_finite_galois_proved,
    S.clauseC.torsion_action_continuous_proved⟩

def initialThetaData_conclusion_clause_c_torsion_basis
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      S.candidate.arithmetic.curve.LTorsion l :=
  S.clauseC.torsion_module_basis

theorem initialThetaData_conclusion_clause_d
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne ∧
      S.candidate.cF.signature = SourceOrbicurveSignature.typeOneOne ∧
      S.candidate.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l ∧
      S.candidate.cK.signature =
        SourceOrbicurveSignature.typeOneLTorsionPlusMinus l ∧
      S.clauseD.signInvolution_squared ∧
      S.clauseD.signQuotient_invariant ∧
      S.clauseD.xK_cK_cover.finite_etale ∧
      S.clauseD.xK_cK_cartesian_square ∧
      S.clauseD.delta_x_open_subgroup ∧
      S.clauseD.delta_c_open_subgroup ∧
      S.clauseD.group_diagram_naturality := by
  exact ⟨S.clauseD.xF_type, S.clauseD.cF_type,
    S.clauseD.xK_type, S.clauseD.cK_type,
    S.clauseD.signInvolution_squared_proved,
    S.clauseD.signQuotient_invariant_proved,
    S.clauseD.xK_cK_cover_finite_etale,
    S.clauseD.xK_cK_cartesian_square_proved,
    S.clauseD.delta_x_open_subgroup_proved,
    S.clauseD.delta_c_open_subgroup_proved,
    S.clauseD.group_diagram_naturality_proved⟩

structure InitialThetaDataClauseEConclusion
    {l : PrimeGeFive} (S : SourceInitialThetaData l) where
  section_data : S.clauseE.V_is_section
  Vnon_definition :
    ∀ v : S.candidate.V,
      v ∈ S.clauseE.Vnon ↔
        NumberFieldPlace.IsFinite (S.candidate.place v)
  Varc_definition :
    ∀ v : S.candidate.V,
      v ∈ S.clauseE.Varc ↔
        NumberFieldPlace.IsInfinite (S.candidate.place v)
  Vbad_definition :
    ∀ v : S.candidate.V,
      v ∈ S.clauseE.Vbad ↔
        S.candidate.placeToMod v ∈
          (NumberFieldPlace.finite '' S.candidate.VbadMod)
  Vgood_definition :
    ∀ v : S.candidate.V,
      v ∈ S.clauseE.Vgood ↔
        S.candidate.placeToMod v ∈
          S.candidate.VgoodMod
  nonarchimedean_archimedean_disjoint :
    Disjoint S.clauseE.Vnon S.clauseE.Varc
  nonarchimedean_archimedean_cover :
    S.clauseE.Vnon ∪ S.clauseE.Varc = Set.univ
  bad_good_disjoint : Disjoint S.clauseE.Vbad S.clauseE.Vgood
  bad_good_cover : S.clauseE.Vbad ∪ S.clauseE.Vgood = Set.univ
  finite_local :
    ∀ i : S.clauseE.placePartition.finiteIndex,
      SourceFiniteLocalData l S.candidate S.clauseE.placePartition i
        S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence
  infinite_local :
    ∀ i : S.clauseE.placePartition.infiniteIndex,
      SourceInfiniteLocalData l S.candidate S.clauseE.placePartition i
        S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence

def initialThetaData_conclusion_clause_e
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    InitialThetaDataClauseEConclusion S where
  section_data := S.clauseE.V_is_section_proved
  Vnon_definition := S.clauseE.Vnon_definition
  Varc_definition := S.clauseE.Varc_definition
  Vbad_definition := S.clauseE.Vbad_definition
  Vgood_definition := S.clauseE.Vgood_definition
  nonarchimedean_archimedean_disjoint := S.clauseE.Vnon_arc_disjoint
  nonarchimedean_archimedean_cover := S.clauseE.Vnon_arc_cover
  bad_good_disjoint := S.clauseE.Vbad_good_disjoint
  bad_good_cover := S.clauseE.Vbad_good_cover
  finite_local := S.clauseE.finiteLocal
  infinite_local := S.clauseE.infiniteLocal

theorem initialThetaData_conclusion_clause_e_classification
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    (∀ v : S.candidate.V,
      v ∈ S.clauseE.Vnon ↔
        NumberFieldPlace.IsFinite (S.candidate.place v)) ∧
      (∀ v : S.candidate.V,
        v ∈ S.clauseE.Varc ↔
          NumberFieldPlace.IsInfinite (S.candidate.place v)) ∧
      (∀ v : S.candidate.V,
        v ∈ S.clauseE.Vbad ↔
          S.candidate.placeToMod v ∈
            (NumberFieldPlace.finite '' S.candidate.VbadMod)) ∧
      (∀ v : S.candidate.V,
        v ∈ S.clauseE.Vgood ↔
          S.candidate.placeToMod v ∈ S.candidate.VgoodMod) ∧
      Disjoint S.clauseE.Vnon S.clauseE.Varc ∧
      S.clauseE.Vnon ∪ S.clauseE.Varc = Set.univ ∧
      Disjoint S.clauseE.Vbad S.clauseE.Vgood ∧
      S.clauseE.Vbad ∪ S.clauseE.Vgood = Set.univ := by
  exact ⟨S.clauseE.Vnon_definition, S.clauseE.Varc_definition,
    S.clauseE.Vbad_definition, S.clauseE.Vgood_definition,
    S.clauseE.Vnon_arc_disjoint, S.clauseE.Vnon_arc_cover,
    S.clauseE.Vbad_good_disjoint, S.clauseE.Vbad_good_cover⟩

theorem initialThetaData_conclusion_clause_f
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    S.clauseF.cusp.nonzero_quotient ∧
      S.clauseF.cusp.canonical_generator ∧
      S.clauseF.cusp_diagram_compatibility := by
  exact ⟨S.clauseF.cusp.nonzero_quotient_proved,
    S.clauseF.cusp.canonical_generator_proved,
    S.clauseF.cusp_diagram_compatibility_proved⟩

def initialThetaData_conclusion_clause_f_derived_orbicurves
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    SourceCuspDerivedOrbicurves l S.candidate S.clauseD :=
  S.clauseF.derivedOrbicurves

/-! The constructor keeps every quantifier visible. -/

def SourceInitialThetaData.ofClauses
    {l : PrimeGeFive}
    (D : SourceInitialThetaCandidate l)
    (A : ClauseA l D)
    (B : ClauseB l D)
    (C : ClauseC l D)
    (E : ClauseD l D)
    (P : ClauseE l D E)
    (F : ClauseF l D E)
    (hArithmetic : Prop)
    (hArithmetic_proved : hArithmetic)
    (hOrder : Prop)
    (hOrder_proved : hOrder) :
    SourceInitialThetaData l where
  candidate := D
  clauseA := A
  clauseB := B
  clauseC := C
  clauseD := E
  clauseE := P
  clauseF := F
  arithmetic_clause_coherence := hArithmetic
  arithmetic_clause_coherence_proved := hArithmetic_proved
  clause_order_coherence := hOrder
  clause_order_coherence_proved := hOrder_proved

theorem SourceInitialThetaData.ofClauses_candidate
    {l : PrimeGeFive}
    (D : SourceInitialThetaCandidate l)
    (A : ClauseA l D) (B : ClauseB l D) (C : ClauseC l D)
    (E : ClauseD l D) (P : ClauseE l D E) (F : ClauseF l D E)
    (hA : Prop) (hAp : hA) (hO : Prop) (hOp : hO) :
    (SourceInitialThetaData.ofClauses D A B C E P F hA hAp hO hOp).candidate = D := rfl

theorem SourceInitialThetaData.ofClauses_clause_a
    {l : PrimeGeFive}
    (D : SourceInitialThetaCandidate l)
    (A : ClauseA l D) (B : ClauseB l D) (C : ClauseC l D)
    (E : ClauseD l D) (P : ClauseE l D E) (F : ClauseF l D E)
    (hA : Prop) (hAp : hA) (hO : Prop) (hOp : hO) :
    (SourceInitialThetaData.ofClauses D A B C E P F hA hAp hO hOp).clauseA = A := rfl

def SourceInitialThetaData.ofClauses_conclusion
    {l : PrimeGeFive}
    (D : SourceInitialThetaCandidate l)
    (A : ClauseA l D) (B : ClauseB l D) (C : ClauseC l D)
    (E : ClauseD l D) (P : ClauseE l D E) (F : ClauseF l D E)
    (hA : Prop) (hAp : hA) (hO : Prop) (hOp : hO) :
    InitialThetaDataConclusion
      (SourceInitialThetaData.ofClauses D A B C E P F hA hAp hO hOp) := by
  exact (SourceInitialThetaData.ofClauses D A B C E P F hA hAp hO hOp).conclusion

/-! ## 10. Reusable clause ledger and universal projections -/

structure SourceInitialThetaClauseLedger
    {l : PrimeGeFive} (S : SourceInitialThetaData l) where
  a_field : HasSqrtNegOne S.candidate.arithmetic.F
  a_curve : S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne
  a_stable :
    ∀ p : NumberField.FinitePlace S.candidate.arithmetic.F,
      S.candidate.arithmetic.curve.HasStableReductionAt p
  b_Vmod_all : S.candidate.Vmod = Set.univ
  b_nonempty : S.candidate.VbadMod.Nonempty
  b_odd :
    ∀ p : NumberField.FinitePlace S.candidate.arithmetic.Fmod,
      p ∈ S.candidate.VbadMod →
      Odd (NumberFieldFinitePlace.residueCharacteristic p)
  b_multiplicative :
    ∀ p : NumberField.FinitePlace S.candidate.arithmetic.F,
      NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod →
      S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p
  b_q :
    ∀ p hp, Nat.Coprime (S.clauseB.qParameter p hp).order l.value
  c_torsion :
    PuncturedEllipticCurve.Torsion23Rational S.candidate.arithmetic.curve
  c_image : S.clauseC.standard_SL2_image ≤
    S.clauseC.galois_representation.range
  c_kernel : S.clauseC.K_kernel_field_compatibility
  d_xK : S.candidate.xK.signature =
    SourceOrbicurveSignature.typeOneLTorsion l
  d_cK : S.candidate.cK.signature =
    SourceOrbicurveSignature.typeOneLTorsionPlusMinus l
  d_cartesian : S.clauseD.xK_cK_cartesian_square
  e_section : S.clauseE.V_is_section
  e_Vnon : ∀ v : S.candidate.V,
    v ∈ S.clauseE.Vnon ↔ NumberFieldPlace.IsFinite (S.candidate.place v)
  e_Varc : ∀ v : S.candidate.V,
    v ∈ S.clauseE.Varc ↔ NumberFieldPlace.IsInfinite (S.candidate.place v)
  e_Vbad : ∀ v : S.candidate.V,
    v ∈ S.clauseE.Vbad ↔
      S.candidate.placeToMod v ∈
        (NumberFieldPlace.finite '' S.candidate.VbadMod)
  e_Vgood : ∀ v : S.candidate.V,
    v ∈ S.clauseE.Vgood ↔
      S.candidate.placeToMod v ∈
        S.candidate.VgoodMod
  e_nonarchimedean_archimedean_disjoint :
    Disjoint S.clauseE.Vnon S.clauseE.Varc
  e_nonarchimedean_archimedean_cover :
    S.clauseE.Vnon ∪ S.clauseE.Varc = Set.univ
  e_bad_good_disjoint : Disjoint S.clauseE.Vbad S.clauseE.Vgood
  e_bad_good_cover : S.clauseE.Vbad ∪ S.clauseE.Vgood = Set.univ
  e_finite :
    ∀ i, SourceFiniteLocalData l S.candidate S.clauseE.placePartition i
      S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence
  e_infinite :
    ∀ i, SourceInfiniteLocalData l S.candidate S.clauseE.placePartition i
      S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence
  f_nonzero : S.clauseF.cusp.nonzero_quotient
  f_canonical : S.clauseF.cusp.canonical_generator
  f_compatible : S.clauseF.cusp_diagram_compatibility

namespace SourceInitialThetaClauseLedger

variable {l : PrimeGeFive} {S : SourceInitialThetaData l}
variable (L : SourceInitialThetaClauseLedger S)
include L

theorem a_field_spec : HasSqrtNegOne S.candidate.arithmetic.F := L.a_field

theorem a_curve_spec :
    S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne := L.a_curve

theorem a_stable_spec
    (p : NumberField.FinitePlace S.candidate.arithmetic.F) :
    S.candidate.arithmetic.curve.HasStableReductionAt p := L.a_stable p

theorem b_nonempty_spec : S.candidate.VbadMod.Nonempty := L.b_nonempty

theorem b_Vmod_all_spec : S.candidate.Vmod = Set.univ := L.b_Vmod_all

theorem b_odd_spec
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) := L.b_odd p hp

theorem b_multiplicative_spec
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p :=
  L.b_multiplicative p hp

theorem b_q_spec
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    Nat.Coprime (S.clauseB.qParameter p hp).order l.value := L.b_q p hp

theorem c_torsion_spec :
    PuncturedEllipticCurve.Torsion23Rational S.candidate.arithmetic.curve :=
  L.c_torsion

theorem c_image_spec : S.clauseC.standard_SL2_image ≤
    S.clauseC.galois_representation.range := L.c_image

theorem c_kernel_spec : S.clauseC.K_kernel_field_compatibility := L.c_kernel

theorem d_xK_spec :
    S.candidate.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l :=
  L.d_xK

theorem d_cK_spec :
    S.candidate.cK.signature =
      SourceOrbicurveSignature.typeOneLTorsionPlusMinus l := L.d_cK

theorem d_cartesian_spec : S.clauseD.xK_cK_cartesian_square := L.d_cartesian

theorem e_section_spec : S.clauseE.V_is_section := L.e_section

theorem e_Vnon_spec (v : S.candidate.V) :
    v ∈ S.clauseE.Vnon ↔ NumberFieldPlace.IsFinite (S.candidate.place v) :=
  L.e_Vnon v

theorem e_Varc_spec (v : S.candidate.V) :
    v ∈ S.clauseE.Varc ↔ NumberFieldPlace.IsInfinite (S.candidate.place v) :=
  L.e_Varc v

theorem e_Vbad_spec (v : S.candidate.V) :
    v ∈ S.clauseE.Vbad ↔
      S.candidate.placeToMod v ∈
        (NumberFieldPlace.finite '' S.candidate.VbadMod) :=
  L.e_Vbad v

theorem e_Vgood_spec (v : S.candidate.V) :
    v ∈ S.clauseE.Vgood ↔
      S.candidate.placeToMod v ∈
        S.candidate.VgoodMod :=
  L.e_Vgood v

theorem e_nonarchimedean_archimedean_disjoint_spec :
    Disjoint S.clauseE.Vnon S.clauseE.Varc :=
  L.e_nonarchimedean_archimedean_disjoint

theorem e_nonarchimedean_archimedean_cover_spec :
    S.clauseE.Vnon ∪ S.clauseE.Varc = Set.univ :=
  L.e_nonarchimedean_archimedean_cover

theorem e_bad_good_disjoint_spec :
    Disjoint S.clauseE.Vbad S.clauseE.Vgood :=
  L.e_bad_good_disjoint

theorem e_bad_good_cover_spec :
    S.clauseE.Vbad ∪ S.clauseE.Vgood = Set.univ :=
  L.e_bad_good_cover

def e_finite_spec (i : S.clauseE.placePartition.finiteIndex) :
    SourceFiniteLocalData l S.candidate S.clauseE.placePartition i
      S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence := L.e_finite i

def e_infinite_spec (i : S.clauseE.placePartition.infiniteIndex) :
    SourceInfiniteLocalData l S.candidate S.clauseE.placePartition i
      S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence :=
  L.e_infinite i

theorem f_nonzero_spec : S.clauseF.cusp.nonzero_quotient := L.f_nonzero

theorem f_canonical_spec : S.clauseF.cusp.canonical_generator := L.f_canonical

theorem f_compatible_spec : S.clauseF.cusp_diagram_compatibility :=
  L.f_compatible

def toConclusion : InitialThetaDataConclusion S where
  source_clause_records := S.all_six_clause_records
  arithmetic_clause_coherence := S.arithmetic_clause_coherence_proved
  clause_order_coherence := S.clause_order_coherence_proved
  clause_a_field_moduli_degree_prime_to_l :=
    S.candidate.fieldModuli_degree_prime_to_l
  clause_a_field_moduli_galois := S.candidate.fieldModuli_is_galois
  clause_a_kernel_field_galois := S.candidate.fieldK_is_galois
  clause_a_algebraic_closure_algebraic :=
    S.candidate.algebraicClosure_is_algebraic
  clause_a_algebraic_closure_alg_closed :=
    S.candidate.algebraicClosure_is_alg_closed
  clause_a_sqrtNegOne := L.a_field
  clause_a_algebraicClosure_field := S.clauseA.algebraicClosure_field_proved
  clause_a_algebraicClosure_algebraic :=
    S.clauseA.algebraicClosure_algebraic_proved
  clause_a_curve_signature := L.a_curve
  clause_a_curve_realization := S.clauseA.curve_realization_proved
  clause_a_stable_everywhere := L.a_stable
  clause_a_elliptic_curve_recovery :=
    S.clauseA.elliptic_curve_recovery_proved
  clause_a_sign_involution_exists := S.clauseA.sign_involution_exists_proved
  clause_a_field_of_moduli := S.clauseA.field_of_moduli_proved
  clause_a_maximal_solvable_extension :=
    S.clauseA.maximal_solvable_extension
  clause_a_maximal_solvable_contains := by
    intro E hfinite hgalois
    exact S.clauseA.maximal_solvable_contains E hfinite hgalois
  clause_a_moduli_place_definition := S.clauseA.moduli_place_definition_proved
  clause_b_Vmod_all := L.b_Vmod_all
  clause_b_bad_nonempty := L.b_nonempty
  clause_b_bad_odd := L.b_odd
  clause_b_bad_is_finite := S.clauseB.bad_is_finite
  clause_b_bad_subset_selected := S.clauseB.bad_subset_selected
  clause_b_multiplicative := L.b_multiplicative
  clause_b_stable_over_bad := S.clauseB.stable_over_bad
  clause_b_q_order_prime_to_l := L.b_q
  clause_b_q_parameter_realizes_curve :=
    S.clauseB.q_parameter_realizes_curve_proved
  clause_b_reduction_base_change_compatibility :=
    S.clauseB.reduction_base_change_compatibility_proved
  clause_c_l_prime := l.prime
  clause_c_l_ge_five := l.ge_five
  clause_c_torsion23 := L.c_torsion
  clause_c_torsion_basis := S.clauseC.torsion_module_basis
  clause_c_representation := S.clauseC.galois_representation_eq_canonical
  clause_c_standard_SL2_image := S.clauseC.standard_SL2_image
  clause_c_standard_SL2_image_spec :=
    S.clauseC.standard_SL2_image_spec_proved
  clause_c_image_contains_SL2 := L.c_image
  clause_c_K_kernel := L.c_kernel
  clause_c_residue_prime_to_l :=
    S.clauseC.l_prime_to_bad_residue_characteristics
  clause_c_q_prime_to_l := S.clauseC.l_prime_to_q_orders
  clause_c_q_order := S.clauseC.q_order
  clause_c_kernel_field_finite_galois :=
    S.clauseC.kernel_field_finite_galois_proved
  clause_c_torsion_action_continuous :=
    S.clauseC.torsion_action_continuous_proved
  clause_d_xF_signature := S.clauseD.xF_type
  clause_d_cF_signature := S.clauseD.cF_type
  clause_d_xK_signature := L.d_xK
  clause_d_cK_signature := L.d_cK
  clause_d_sign_involution_map := S.clauseD.signInvolution
  clause_d_sign_quotient_map := S.clauseD.signQuotient
  clause_d_xK_to_xF := S.clauseD.xK_to_xF
  clause_d_cK_to_cF := S.clauseD.cK_to_cF
  clause_d_xK_cK_cover_map := S.clauseD.xK_cK_cover
  clause_d_sign_involution := S.clauseD.signInvolution_squared_proved
  clause_d_sign_quotient := S.clauseD.signQuotient_invariant_proved
  clause_d_cover_finite_etale := S.clauseD.xK_cK_cover_finite_etale
  clause_d_cartesian := L.d_cartesian
  clause_d_cK_determines_xK := S.clauseD.cK_determines_xK
  clause_d_xF_exact_sequence := S.clauseD.xF_exact_sequence
  clause_d_cF_exact_sequence := S.clauseD.cF_exact_sequence
  clause_d_xK_exact_sequence := S.clauseD.xK_exact_sequence
  clause_d_cK_exact_sequence := S.clauseD.cK_exact_sequence
  clause_d_xF_cF_group_inclusion := S.clauseD.xF_cF_group_inclusion
  clause_d_xK_xF_group_inclusion := S.clauseD.xK_xF_group_inclusion
  clause_d_cK_cF_group_inclusion := S.clauseD.cK_cF_group_inclusion
  clause_d_delta_x_open := S.clauseD.delta_x_open_subgroup_proved
  clause_d_delta_c_open := S.clauseD.delta_c_open_subgroup_proved
  clause_d_group_naturality := S.clauseD.group_diagram_naturality_proved
  clause_e_section := L.e_section
  clause_e_place_partition := S.clauseE.placePartition
  clause_e_Vnon := S.clauseE.Vnon
  clause_e_Varc := S.clauseE.Varc
  clause_e_Vbad := S.clauseE.Vbad
  clause_e_Vgood := S.clauseE.Vgood
  clause_e_Vnon_definition := L.e_Vnon
  clause_e_Varc_definition := L.e_Varc
  clause_e_Vbad_definition := L.e_Vbad
  clause_e_Vgood_definition := L.e_Vgood
  clause_e_nonarchimedean_archimedean_disjoint :=
    L.e_nonarchimedean_archimedean_disjoint
  clause_e_nonarchimedean_archimedean_cover :=
    L.e_nonarchimedean_archimedean_cover
  clause_e_bad_good_disjoint := L.e_bad_good_disjoint
  clause_e_bad_good_cover := L.e_bad_good_cover
  clause_e_finite_local := L.e_finite
  clause_e_infinite_local := L.e_infinite
  clause_e_finite_local_curve_diagram :=
    S.clauseE.finite_local_curve_diagram_proved
  clause_e_infinite_local_curve_diagram :=
    S.clauseE.infinite_local_curve_diagram_proved
  clause_e_bad_local_orbicurve_type :=
    S.clauseE.bad_local_orbicurve_type_proved
  clause_e_good_local_orbicurve_type :=
    S.clauseE.good_local_orbicurve_type_proved
  clause_e_decomposition_group_naturality :=
    S.clauseE.decomposition_group_naturality_proved
  clause_e_local_group_projection_compatibility :=
    S.clauseE.local_group_projection_compatibility_proved
  clause_f_derived_orbicurves := S.clauseF.derivedOrbicurves
  clause_f_cusp := S.clauseF.cusp
  clause_f_cusp_sign_ambiguity := S.clauseF.cusp.sign_ambiguity_proved
  clause_f_cusp_lies_on_cK := S.clauseF.cusp_lies_on_cK_proved
  clause_f_cusp_from_nonzero_Q := S.clauseF.cusp_from_nonzero_Q_proved
  clause_f_cusp_localization := S.clauseF.cusp_localization_proved
  clause_f_bad_cusp_canonical_generator :=
    S.clauseF.bad_cusp_canonical_generator_proved
  clause_f_good_cusp_compatibility :=
    S.clauseF.good_cusp_compatibility_proved
  clause_f_cusp_sign_independence := S.clauseF.cusp_sign_independence_proved
  clause_f_cusp_nonzero := L.f_nonzero
  clause_f_cusp_canonical := L.f_canonical
  clause_f_cusp_compatibility := L.f_compatible

end SourceInitialThetaClauseLedger

def SourceInitialThetaData.toLedger
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    SourceInitialThetaClauseLedger S where
  a_field := S.clauseA.squareRootNegOne
  a_curve := S.clauseA.curve_is_once_punctured_elliptic
  a_stable := S.clauseA.stable_reduction_everywhere
  b_Vmod_all := S.candidate.Vmod_eq_univ
  b_nonempty := S.clauseB.bad_nonempty
  b_odd := S.clauseB.bad_odd_residue_characteristic
  b_multiplicative := S.clauseB.multiplicative_over_bad
  b_q := S.clauseB.q_order_prime_to_l
  c_torsion := S.clauseC.torsion23_rational
  c_image := S.clauseC.image_contains_SL2
  c_kernel := S.clauseC.K_kernel_field_compatibility_proved
  d_xK := S.clauseD.xK_type
  d_cK := S.clauseD.cK_type
  d_cartesian := S.clauseD.xK_cK_cartesian_square_proved
  e_section := S.clauseE.V_is_section_proved
  e_Vnon := S.clauseE.Vnon_definition
  e_Varc := S.clauseE.Varc_definition
  e_Vbad := S.clauseE.Vbad_definition
  e_Vgood := S.clauseE.Vgood_definition
  e_nonarchimedean_archimedean_disjoint := S.clauseE.Vnon_arc_disjoint
  e_nonarchimedean_archimedean_cover := S.clauseE.Vnon_arc_cover
  e_bad_good_disjoint := S.clauseE.Vbad_good_disjoint
  e_bad_good_cover := S.clauseE.Vbad_good_cover
  e_finite := S.clauseE.finiteLocal
  e_infinite := S.clauseE.infiniteLocal
  f_nonzero := S.clauseF.cusp.nonzero_quotient_proved
  f_canonical := S.clauseF.cusp.canonical_generator_proved
  f_compatible := S.clauseF.cusp_diagram_compatibility_proved

theorem SourceInitialThetaData.toLedger_toConclusion
    {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    S.toLedger.toConclusion = S.conclusion := by
  rfl

def initialThetaData_conclusion_via_ledger
    {l : PrimeGeFive} :
    ∀ S : SourceInitialThetaData l,
      InitialThetaDataConclusion S := by
  intro S
  exact S.toLedger.toConclusion

/-! ## 11. Place-indexed consequences retained for reuse downstream -/

namespace SourceInitialThetaCandidate

variable {l : PrimeGeFive} (D : SourceInitialThetaCandidate l)

theorem placeToMod_mem_selected (v : D.V) : D.placeToMod v ∈ D.Vmod :=
  D.placeToMod_mem_Vmod v

theorem placeToMod_image_subset :
    Set.range D.placeToMod ⊆ D.Vmod := by
  intro x hx
  rcases hx with ⟨v, rfl⟩
  exact D.placeToMod_mem_selected v

theorem selected_place_has_preimage (p : D.Vmod) :
    ∃ v : D.V, D.placeToMod v = p := by
  rcases D.placeToMod_surjective p with ⟨v, hv⟩
  exact ⟨v, hv⟩

theorem selected_place_preimage_unique {v w : D.V}
    (h : D.placeToMod v = D.placeToMod w) : v = w :=
  D.placeToMod_injective h

theorem place_comap_selected (v : D.V) :
    NumberFieldPlace.comap (k := D.arithmetic.Fmod) (D.place v) =
      D.placeToMod v :=
  D.place_comap_compatible v

theorem place_comap_selected_mem (v : D.V) :
    NumberFieldPlace.comap (D.place v) ∈ D.Vmod := by
  rw [D.place_comap_selected]
  exact D.placeToMod_mem_selected v

theorem finite_bad_selected (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) : NumberFieldPlace.finite p ∈ D.Vmod :=
  D.badMod_subset_Vmod p hp

theorem finite_bad_selected_preimage
    (p : NumberField.FinitePlace D.arithmetic.Fmod)
    (hp : p ∈ D.VbadMod) :
    ∃ v : D.V, D.placeToMod v = NumberFieldPlace.finite p := by
  rcases D.selected_place_has_preimage
      ⟨NumberFieldPlace.finite p, D.finite_bad_selected p hp⟩ with ⟨v, hv⟩
  exact ⟨v, hv⟩

theorem place_map_round_trip (v : D.V) :
    NumberFieldPlace.comap (k := D.arithmetic.Fmod) (D.place v) =
      D.placeToMod v :=
  D.place_comap_compatible v

theorem place_map_injective_on_range {v w : D.V}
    (h : NumberFieldPlace.comap (k := D.arithmetic.Fmod) (D.place v) =
      NumberFieldPlace.comap (k := D.arithmetic.Fmod) (D.place w)) : v = w := by
  apply D.placeToMod_injective
  rw [← D.place_comap_selected v, ← D.place_comap_selected w, h]

theorem Vmod_image_eq_of_surjective :
    Set.range D.placeToMod = D.Vmod := by
  apply Set.Subset.antisymm
  · exact D.placeToMod_image_subset
  · intro p hp
    rcases D.selected_place_has_preimage ⟨p, hp⟩ with ⟨v, hv⟩
    exact ⟨v, hv⟩

theorem Vmod_image_eq_of_bijective :
    Set.range D.placeToMod = D.Vmod := D.Vmod_image_eq_of_surjective

theorem selected_partition_preserves_comap
    (P : SourcePlacePartition l D)
    (i : P.finiteIndex) :
    NumberFieldPlace.comap (k := D.arithmetic.Fmod)
      (D.place (P.finiteToV i)) =
      D.placeToMod (P.finiteToV i) := by
  exact D.place_comap_selected (P.finiteToV i)

theorem selected_partition_finite_moduli
    (P : SourcePlacePartition l D)
    (i : P.finiteIndex) :
    D.placeToMod (P.finiteToV i) =
      NumberFieldPlace.finite
        (NumberFieldFinitePlace.comap (P.finitePlace i)) :=
  P.finite_moduli_compatibility i

theorem selected_partition_infinite_moduli
    (P : SourcePlacePartition l D)
    (i : P.infiniteIndex) :
    D.placeToMod (P.infiniteToV i) =
      NumberFieldPlace.infinite
        ((P.infinitePlace i).comap
          (algebraMap D.arithmetic.Fmod D.arithmetic.K)) :=
  P.infinite_moduli_compatibility i

end SourceInitialThetaCandidate


end InitialThetaSource

end

end LeanFormal.IUT
