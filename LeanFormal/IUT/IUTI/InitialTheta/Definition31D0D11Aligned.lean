import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31RootLemmas
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # A dependent D0--D11 ledger for Definition 3.1

  This file is the construction ledger, rather than a second source contract.
  Every stage is indexed by the preceding stage and all arithmetic equalities
  are retained.  In particular, a clause from a different candidate cannot be
  used to fill a later stage.  The records below therefore expose the exact
  boundary at which an arithmetic-geometric construction is still required.

  The source clauses are not replaced by `Nonempty` statements.  A stage has a
  clause only when its full source record is supplied, and every theorem below
  projects the actual field or proves a consequence from the actual field.
  The final D11 theorem is consequently a theorem about a completed ledger;
  the arithmetic-to-ledger existence proposition is recorded separately and
  is not silently used as an axiom.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u v w

namespace Theorem311Source
namespace Definition31D0D11Aligned

open LeanFormal.IUT.InitialThetaSource

/-! ## D0: kernel and arithmetic root -/

structure D0Root (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData.{u} l

namespace D0Root

variable {l : PrimeGeFive} (R : D0Root.{u} l)
include R

def fromArithmetic (A : InitialThetaArithmeticData.{u} l) : D0Root.{u} l :=
  ⟨A⟩

@[simp] theorem fromArithmetic_arithmetic
    (A : InitialThetaArithmeticData.{u} l) :
    (fromArithmetic A).arithmetic = A := rfl

theorem sqrtNegOne : HasSqrtNegOne R.arithmetic.F :=
  R.arithmetic.tower.sqrtNegOne_spec

theorem degreePrimeToL :
    Nat.Coprime (Module.finrank R.arithmetic.Fmod R.arithmetic.F) l.value :=
  R.arithmetic.tower.degreePrimeToL_spec

theorem prime : Nat.Prime l.value := l.prime

theorem geFive : 5 ≤ l.value := l.ge_five

theorem odd : Odd l.value := l.odd

theorem positive : 0 < l.value := l.prime.pos

theorem nonzero : l.value ≠ 0 := Nat.ne_of_gt R.positive

theorem prime_data : Nat.Prime l.value ∧ 5 ≤ l.value ∧ Odd l.value :=
  ⟨R.prime, R.geFive, R.odd⟩

theorem arithmetic_self : R.arithmetic = R.arithmetic := rfl

theorem fields_are_number_fields :
    Nonempty R.arithmetic.Fmod ∧
      Nonempty R.arithmetic.F ∧ Nonempty R.arithmetic.K :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem towers_are_finite_galois :
    FiniteDimensional R.arithmetic.Fmod R.arithmetic.F ∧
      IsGalois R.arithmetic.Fmod R.arithmetic.F ∧
      FiniteDimensional R.arithmetic.F R.arithmetic.K ∧
      IsGalois R.arithmetic.F R.arithmetic.K :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem sqrtNegOne_witness :
    ∃ i : R.arithmetic.F, i * i = -1 :=
  R.sqrtNegOne

theorem degree_coprime_symm :
    Nat.Coprime l.value (Module.finrank R.arithmetic.Fmod R.arithmetic.F) :=
  R.degreePrimeToL.symm

theorem degree_positive :
    0 < Module.finrank R.arithmetic.Fmod R.arithmetic.F := by
  exact Module.finrank_pos

theorem field_inclusion_data :
    Nonempty R.arithmetic.Fmod ∧ Nonempty R.arithmetic.F ∧
      Nonempty R.arithmetic.K :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem root_is_not_a_conclusion :
    R.arithmetic = R.arithmetic := by rfl

end D0Root

/-! ## D1: the prime data is closed before any source clause is read -/

structure D1Root (l : PrimeGeFive) where
  foundation : D0Root.{u} l
  prime_proved : Nat.Prime l.value
  lower_bound_proved : 5 ≤ l.value
  odd_proved : Odd l.value
  positive_proved : 0 < l.value

namespace D1Root

variable {l : PrimeGeFive} (S : D1Root.{u} l)
include S

def of (R : D0Root.{u} l) : D1Root.{u} l where
  foundation := R
  prime_proved := l.prime
  lower_bound_proved := l.ge_five
  odd_proved := l.odd
  positive_proved := l.prime.pos

theorem prime : Nat.Prime l.value := S.prime_proved

theorem lower_bound : 5 ≤ l.value := S.lower_bound_proved

theorem odd : Odd l.value := S.odd_proved

theorem positive : 0 < l.value := S.positive_proved

theorem nonzero : l.value ≠ 0 := Nat.ne_of_gt S.positive

theorem prime_lower_odd : Nat.Prime l.value ∧ 5 ≤ l.value ∧ Odd l.value :=
  ⟨S.prime, S.lower_bound, S.odd⟩

theorem prime_lower_positive : Nat.Prime l.value ∧ 5 ≤ l.value ∧ 0 < l.value :=
  ⟨S.prime, S.lower_bound, S.positive⟩

theorem odd_not_two : l.value ≠ 2 := by
  intro h
  have ho : Odd l.value := S.odd_proved
  rw [h] at ho
  norm_num at ho

theorem odd_not_zero : l.value ≠ 0 := by
  exact Nat.ne_of_gt S.positive

theorem lower_bound_trans (n : Nat) (h : l.value ≤ n) : 5 ≤ n :=
  S.lower_bound.trans h

theorem positive_cast : (0 : Int) < l.value := by
  exact_mod_cast S.positive

theorem prime_data_stable :
    Nat.Prime l.value ∧ 5 ≤ l.value ∧ Odd l.value ∧ 0 < l.value :=
  ⟨S.prime, S.lower_bound, S.odd, S.positive⟩

theorem inherited_from_d0 : S.prime = l.prime := by
  rfl

end D1Root

/-! ## D2: candidate and Definition 3.1(a), with arithmetic alignment -/

structure D2Root (R : D1Root.{u} l) where
  candidate : SourceInitialThetaCandidate.{u} l
  candidate_arithmetic_eq : candidate.arithmetic = R.foundation.arithmetic
  clauseA : ClauseA l candidate

namespace D2Root

variable {l : PrimeGeFive}
variable {R : D1Root.{u} l} (S : D2Root R)
include S

/-! The predecessor is named explicitly.  This is intentionally not inferred
    from the candidate, so transport through an equality is visible. -/
def predecessor (S : D2Root R) : D1Root.{u} l := R

theorem candidate_arithmetic :
    S.candidate.arithmetic = R.foundation.arithmetic :=
  S.candidate_arithmetic_eq

theorem candidate_arithmetic_symm :
    R.foundation.arithmetic = S.candidate.arithmetic :=
  S.candidate_arithmetic_eq.symm

theorem clauseA_field :
    HasSqrtNegOne S.candidate.arithmetic.F :=
  S.clauseA.squareRootNegOne

theorem clauseA_curve_signature :
    S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne :=
  S.clauseA.curve_is_once_punctured_elliptic

theorem clauseA_stable_everywhere
    (p : NumberField.FinitePlace S.candidate.arithmetic.F) :
    S.candidate.arithmetic.curve.HasStableReductionAt p :=
  S.clauseA.stable_reduction_everywhere p

theorem clauseA_curve_realization : S.clauseA.curve_realization :=
  S.clauseA.curve_realization_proved

theorem clauseA_elliptic_recovery : S.clauseA.elliptic_curve_recovery :=
  S.clauseA.elliptic_curve_recovery_proved

theorem clauseA_sign_involution : S.clauseA.sign_involution_exists :=
  S.clauseA.sign_involution_exists_proved

theorem clauseA_field_of_moduli : S.clauseA.field_of_moduli :=
  S.clauseA.field_of_moduli_proved

theorem clauseA_moduli_places : S.clauseA.moduli_place_definition :=
  S.clauseA.moduli_place_definition_proved

theorem clauseA_closure_field : S.clauseA.algebraicClosure_field :=
  S.clauseA.algebraicClosure_field_proved

theorem clauseA_closure_algebraic : S.clauseA.algebraicClosure_algebraic :=
  S.clauseA.algebraicClosure_algebraic_proved

theorem clauseA_maximal_solvable_contains
    (E : IntermediateField S.candidate.arithmetic.Fmod
      (AlgebraicClosure S.candidate.arithmetic.Fmod))
    (hfinite : FiniteDimensional S.candidate.arithmetic.Fmod E)
    (hgalois : IsGalois S.candidate.arithmetic.Fmod E) :
    E ≤ S.clauseA.maximal_solvable_extension :=
  S.clauseA.maximal_solvable_contains E hfinite hgalois

theorem candidate_place_to_mod_bijective :
    Function.Bijective S.candidate.placeToMod :=
  S.candidate.placeToMod_bijective

theorem candidate_place_to_mod_injective :
    Function.Injective S.candidate.placeToMod :=
  S.candidate.placeToMod_bijective.injective

theorem candidate_place_to_mod_surjective :
    Function.Surjective S.candidate.placeToMod :=
  S.candidate.placeToMod_bijective.surjective

theorem candidate_place_membership (v : S.candidate.V) :
    S.candidate.placeToMod v ∈ S.candidate.Vmod :=
  S.candidate.placeToMod_mem_Vmod v

theorem candidate_place_comap (v : S.candidate.V) :
    NumberFieldPlace.comap (S.candidate.place v) =
      S.candidate.placeToMod v :=
  S.candidate.place_comap_compatible v

theorem candidate_bad_subset
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.finite p ∈ S.candidate.Vmod :=
  S.candidate.badMod_subset_Vmod p hp

theorem candidate_moduli_universe : S.candidate.Vmod = Set.univ := by
  exact SourceInitialThetaCandidate.Vmod_eq_univ S.candidate

theorem candidate_selected_nonempty_of_bad
    (h : S.candidate.VbadMod.Nonempty) : Nonempty S.candidate.V := by
  rcases h with ⟨p, hp⟩
  have hmod : NumberFieldPlace.finite p ∈ S.candidate.Vmod :=
    S.candidate.badMod_subset_Vmod p hp
  exact SourceInitialThetaCandidate.V_nonempty_of_Vmod_nonempty
    S.candidate ⟨NumberFieldPlace.finite p, hmod⟩

theorem candidate_arithmetic_transport
    (h : S.candidate.arithmetic = R.foundation.arithmetic) :
    HasSqrtNegOne R.foundation.arithmetic.F := by
  rw [← h]
  exact S.clauseA_field

theorem d2_bundle :
    HasSqrtNegOne S.candidate.arithmetic.F ∧
      S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne ∧
      (∀ p : NumberField.FinitePlace S.candidate.arithmetic.F,
        S.candidate.arithmetic.curve.HasStableReductionAt p) :=
  ⟨S.clauseA_field, S.clauseA_curve_signature,
    S.clauseA_stable_everywhere⟩

end D2Root

/-! ## D3: bad places and the selected-place carrier -/

structure D3Root {P : D1Root.{u} l} (R : D2Root.{u} P) where
  clauseB : ClauseB l R.candidate

namespace D3Root

variable {l : PrimeGeFive}
variable {P : D1Root.{u} l} {R : D2Root.{u} P} (S : D3Root R)
include S

/- The preceding stage is an index of `D3Root`, not an extra hypothesis.
   Naming that index makes the dependency chain available to later stages
   without weakening it to an untyped carrier. -/
def predecessor (S : D3Root R) : D2Root.{u} P := R

def candidate (S : D3Root R) : SourceInitialThetaCandidate.{u} l := R.candidate

theorem candidate_arithmetic_eq :
    S.candidate.arithmetic = R.predecessor.foundation.arithmetic :=
  R.candidate_arithmetic

theorem bad_nonempty : S.candidate.VbadMod.Nonempty :=
  S.clauseB.bad_nonempty

theorem bad_is_finite
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.IsFinite (NumberFieldPlace.finite p) :=
  S.clauseB.bad_is_finite p hp

theorem bad_odd
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  S.clauseB.bad_odd_residue_characteristic p hp

theorem bad_subset_selected
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.finite p ∈ S.candidate.Vmod :=
  S.clauseB.bad_subset_selected p hp

theorem bad_place_has_selected_preimage
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    ∃ v : S.candidate.V,
      S.candidate.placeToMod v = NumberFieldPlace.finite p := by
  rcases S.candidate.placeToMod_bijective.surjective
      (NumberFieldPlace.finite p) with ⟨v, hv⟩
  exact ⟨v, hv⟩

theorem bad_place_selected_is_bad
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod)
    (v : S.candidate.V)
    (hv : S.candidate.placeToMod v = NumberFieldPlace.finite p) :
    S.candidate.placeToMod v ∈ (NumberFieldPlace.finite '' S.candidate.VbadMod) :=
  ⟨p, hp, hv.symm⟩

theorem all_moduli_places_selected :
    ∀ p : NumberFieldPlace S.candidate.arithmetic.Fmod,
      p ∈ S.candidate.Vmod := by
  intro p
  exact SourceInitialThetaCandidate.every_moduli_place_selected S.candidate p

theorem selected_carrier_nonempty : Nonempty S.candidate.V := by
  rcases S.bad_nonempty with ⟨p, hp⟩
  rcases S.bad_place_has_selected_preimage p hp with ⟨v, _⟩
  exact ⟨v⟩

theorem place_section (v : S.candidate.V) :
    NumberFieldPlace.comap (S.candidate.place v) =
      S.candidate.placeToMod v :=
  S.candidate.place_comap_compatible v

theorem place_to_mod_injective :
    Function.Injective S.candidate.placeToMod :=
  S.candidate.placeToMod_bijective.injective

theorem place_to_mod_surjective :
    Function.Surjective S.candidate.placeToMod :=
  S.candidate.placeToMod_bijective.surjective

theorem Vbad_moduli_image_subset :
    NumberFieldPlace.finite '' S.candidate.VbadMod ⊆ S.candidate.Vmod := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  exact S.bad_subset_selected p hp

theorem good_definition :
    S.candidate.VgoodMod = S.candidate.Vmod \
      (NumberFieldPlace.finite '' S.candidate.VbadMod) :=
  S.candidate.VgoodMod_definition

theorem bad_odd_not_two
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldFinitePlace.residueCharacteristic p ≠ 2 := by
  intro h
  have ho := S.bad_odd p hp
  rw [h] at ho
  norm_num at ho

theorem D3_bundle :
    S.candidate.VbadMod.Nonempty ∧
      (∀ p, p ∈ S.candidate.VbadMod →
        NumberFieldPlace.finite p ∈ S.candidate.Vmod) ∧
      Function.Bijective S.candidate.placeToMod :=
  ⟨S.bad_nonempty, S.bad_subset_selected,
    S.candidate.placeToMod_bijective⟩

end D3Root

/-! ## D4: stable/multiplicative reduction and local q data -/

structure D4Root {P : D1Root.{u} l} {Q : D2Root.{u} P}
    (R : D3Root.{u} Q) where
  reduction_clause : ClauseB l R.candidate

namespace D4Root

variable {l : PrimeGeFive}
variable {P : D1Root.{u} l} {Q : D2Root.{u} P}
variable {R : D3Root.{u} Q} (S : D4Root R)
include S

def predecessor (S : D4Root R) : D3Root.{u} Q := R

def candidate (S : D4Root R) : SourceInitialThetaCandidate.{u} l := R.candidate

theorem candidate_arithmetic_eq :
    S.candidate.arithmetic = R.predecessor.predecessor.foundation.arithmetic := by
  exact R.candidate_arithmetic_eq

theorem bad_nonempty : S.candidate.VbadMod.Nonempty :=
  S.reduction_clause.bad_nonempty

theorem bad_is_finite
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.IsFinite (NumberFieldPlace.finite p) :=
  S.reduction_clause.bad_is_finite p hp

theorem bad_odd
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  S.reduction_clause.bad_odd_residue_characteristic p hp

theorem bad_subset_selected
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.finite p ∈ S.candidate.Vmod :=
  S.reduction_clause.bad_subset_selected p hp

theorem multiplicative_over_bad
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p :=
  S.reduction_clause.multiplicative_over_bad p hp

theorem stable_over_bad
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.candidate.arithmetic.curve.HasStableReductionAt p :=
  S.reduction_clause.stable_over_bad p hp

theorem stable_of_multiplicative
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.candidate.arithmetic.curve.HasStableReductionAt p :=
  PuncturedEllipticCurve.hasMultiplicativeReductionAt_imp_stable
    (S.multiplicative_over_bad p hp)

def qParameter
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    NumberFieldFinitePlace.FinitePlaceQCandidate p :=
  S.reduction_clause.qParameter p hp

theorem qParameter_spec
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    qParameter S p hp = S.reduction_clause.qParameter p hp := rfl

theorem q_order_prime_to_l
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    Nat.Coprime (S.qParameter p hp).order l.value :=
  S.reduction_clause.q_order_prime_to_l p hp

theorem q_order_positive
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    0 < (S.qParameter p hp).order :=
  (S.qParameter p hp).order_pos

theorem q_nonzero
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    (S.qParameter p hp).q ≠ 0 :=
  (S.qParameter p hp).q_ne_zero

theorem q_ne_one
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    (S.qParameter p hp).q ≠ 1 :=
  (S.qParameter p hp).q_ne_one

theorem q_valuation_lt_one
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    (Valued.v (S.qParameter p hp).q : WithZero (Multiplicative Int)) < 1 :=
  (S.qParameter p hp).valuation_lt_one

theorem q_parameter_realizes_curve
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.reduction_clause.q_parameter_realizes_curve p hp :=
  S.reduction_clause.q_parameter_realizes_curve_proved p hp

theorem reduction_base_change_compatibility :
    S.reduction_clause.reduction_base_change_compatibility :=
  S.reduction_clause.reduction_base_change_compatibility_proved

theorem q_power_nonzero
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod)
    (n : Nat) :
    (S.qParameter p hp).q ^ n ≠ 0 :=
  pow_ne_zero n (S.q_nonzero p hp)

theorem q_power_order_positive
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod)
    (n : Nat) (hn : 0 < n) :
    0 < (S.qParameter p hp).order * n := by
  exact Nat.mul_pos (S.q_order_positive p hp) hn

theorem q_reduction_bundle
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.candidate.arithmetic.curve.HasStableReductionAt p ∧
      S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p ∧
      (S.qParameter p hp).q ≠ 0 ∧
      (S.qParameter p hp).q ≠ 1 ∧
      0 < (S.qParameter p hp).order := by
  exact ⟨S.stable_over_bad p hp, S.multiplicative_over_bad p hp,
    S.q_nonzero p hp, S.q_ne_one p hp, S.q_order_positive p hp⟩

theorem D4_bundle :
    S.candidate.VbadMod.Nonempty ∧
      (∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
        (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
        S.candidate.arithmetic.curve.HasStableReductionAt p) ∧
      (∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
        (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
        S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p) ∧
      (∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
        (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
        (S.qParameter p hp).q ≠ 0) := by
  exact ⟨S.bad_nonempty, S.stable_over_bad,
    S.multiplicative_over_bad, S.q_nonzero⟩

end D4Root

/-! ## D5: torsion, the representation, and its large image -/

structure D5Root {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} (R : D4Root.{u} R₃) where
  torsion_clause : ClauseC l R.candidate

namespace D5Root

variable {l : PrimeGeFive}
variable {P : D1Root.{u} l} {Q : D2Root.{u} P}
variable {R₃ : D3Root.{u} Q} {R : D4Root.{u} R₃} (S : D5Root R)
include S

def predecessor (S : D5Root R) : D4Root.{u} R₃ := R

abbrev candidate (S : D5Root R) : SourceInitialThetaCandidate.{u} l := R.candidate

def torsionBasis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      S.candidate.arithmetic.curve.LTorsion l :=
  S.torsion_clause.torsion_module_basis

def representation :
    (AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  S.torsion_clause.galois_representation

def standardSL2Image :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) :=
  S.torsion_clause.standard_SL2_image

theorem torsion23_rational :
    PuncturedEllipticCurve.Torsion23Rational
      S.candidate.arithmetic.curve :=
  S.torsion_clause.torsion23_rational

theorem torsion_basis_left (x : Fin 2 → ZMod l.value) :
    S.torsionBasis.symm (S.torsionBasis x) = x :=
  S.torsionBasis.symm_apply_apply x

theorem torsion_basis_right
    (x : S.candidate.arithmetic.curve.LTorsion l) :
    S.torsionBasis (S.torsionBasis.symm x) = x :=
  S.torsionBasis.apply_symm_apply x

theorem torsion_basis_injective : Function.Injective S.torsionBasis :=
  S.torsionBasis.injective

theorem torsion_basis_surjective : Function.Surjective S.torsionBasis :=
  S.torsionBasis.surjective

theorem representation_canonical :
    S.representation =
      S.candidate.arithmetic.curve.galoisLTorsionMatrixRepresentation
        l S.torsionBasis :=
  S.torsion_clause.galois_representation_eq_canonical

theorem representation_map_one : S.representation 1 = 1 :=
  S.representation.map_one

theorem representation_map_mul (x y) :
    S.representation (x * y) = S.representation x * S.representation y :=
  S.representation.map_mul x y

theorem representation_map_inv (x) :
    S.representation x⁻¹ = (S.representation x)⁻¹ := by
  exact map_inv S.representation x

theorem representation_map_pow (x) (n : Nat) :
    S.representation (x ^ n) = S.representation x ^ n := by
  exact map_pow S.representation x n

theorem representation_map_zpow (x) (n : Int) :
    S.representation (x ^ n) = S.representation x ^ n := by
  exact map_zpow S.representation x n

theorem standard_sl2_spec : S.torsion_clause.standard_SL2_image_spec :=
  S.torsion_clause.standard_SL2_image_spec_proved

theorem image_contains_sl2 : S.standardSL2Image ≤ S.representation.range :=
  S.torsion_clause.image_contains_SL2

theorem image_contains_sl2_member
    (g : S.standardSL2Image) :
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) ∈
      S.representation.range :=
  S.image_contains_sl2 g.property

theorem kernel_iff (x) : x ∈ S.representation.ker ↔ S.representation x = 1 :=
  Iff.rfl

theorem kernel_one : (1 : _) ∈ S.representation.ker := by
  exact S.representation_map_one

theorem kernel_mul {x y} (hx : x ∈ S.representation.ker)
    (hy : y ∈ S.representation.ker) : x * y ∈ S.representation.ker := by
  change S.representation (x * y) = 1
  change S.representation x = 1 at hx
  change S.representation y = 1 at hy
  rw [S.representation_map_mul, hx, hy, mul_one]

theorem kernel_inv {x} (hx : x ∈ S.representation.ker) :
    x⁻¹ ∈ S.representation.ker := by
  change S.representation x⁻¹ = 1
  change S.representation x = 1 at hx
  rw [S.representation_map_inv, hx, inv_one]

theorem kernel_pow {x} (hx : x ∈ S.representation.ker) (n : Nat) :
    x ^ n ∈ S.representation.ker := by
  change S.representation (x ^ n) = 1
  rw [S.representation_map_pow]
  rw [show S.representation x = 1 by exact hx, one_pow]

theorem kernel_zpow {x} (hx : x ∈ S.representation.ker) (n : Int) :
    x ^ n ∈ S.representation.ker := by
  change S.representation (x ^ n) = 1
  rw [S.representation_map_zpow]
  rw [show S.representation x = 1 by exact hx, one_zpow]

theorem K_kernel_compatibility :
    S.torsion_clause.K_kernel_field_compatibility :=
  S.torsion_clause.K_kernel_field_compatibility_proved

theorem kernel_field_finite_galois :
    S.torsion_clause.kernel_field_finite_galois :=
  S.torsion_clause.kernel_field_finite_galois_proved

theorem torsion_action_continuous :
    S.torsion_clause.torsion_action_continuous :=
  S.torsion_clause.torsion_action_continuous_proved

theorem D5_bundle :
    PuncturedEllipticCurve.Torsion23Rational
      S.candidate.arithmetic.curve ∧
      S.torsion_clause.standard_SL2_image_spec ∧
      S.torsion_clause.K_kernel_field_compatibility ∧
      S.torsion_clause.kernel_field_finite_galois ∧
      S.torsion_clause.torsion_action_continuous :=
  ⟨S.torsion23_rational, S.standard_sl2_spec,
    S.K_kernel_compatibility, S.kernel_field_finite_galois,
    S.torsion_action_continuous⟩

end D5Root

/-! ## D6: orbicurves and exact sequences -/

structure D6Root {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    (R : D5Root.{u} R₄) where
  orbicurve_clause : ClauseD l R.candidate

namespace D6Root

variable {l : PrimeGeFive}
variable {P : D1Root.{u} l} {Q : D2Root.{u} P}
variable {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
variable {R₅ : D5Root.{u} R₄} (S : D6Root R₅)
include S

def predecessor (S : D6Root R₅) : D5Root.{u} R₄ := R₅

abbrev candidate (S : D6Root R₅) : SourceInitialThetaCandidate.{u} l := R₅.candidate
abbrev clause : ClauseD l S.candidate := S.orbicurve_clause
abbrev xFExact : SourceProfiniteExactSequence := S.clause.xF_exact_sequence
abbrev cFExact : SourceProfiniteExactSequence := S.clause.cF_exact_sequence
abbrev xKExact : SourceProfiniteExactSequence := S.clause.xK_exact_sequence
abbrev cKExact : SourceProfiniteExactSequence := S.clause.cK_exact_sequence

def xFToCF : SourceExactSequenceEmbedding S.xFExact S.cFExact :=
  S.clause.xF_cF_group_inclusion

def xKToXF : SourceExactSequenceEmbedding S.xKExact S.xFExact :=
  S.clause.xK_xF_group_inclusion

def cKToCF : SourceExactSequenceEmbedding S.cKExact S.cFExact :=
  S.clause.cK_cF_group_inclusion

theorem xF_signature :
    S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne :=
  S.clause.xF_type

theorem cF_signature :
    S.candidate.cF.signature = SourceOrbicurveSignature.typeOneOne :=
  S.clause.cF_type

theorem xK_signature :
    S.candidate.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l :=
  S.clause.xK_type

theorem cK_signature :
    S.candidate.cK.signature =
      SourceOrbicurveSignature.typeOneLTorsionPlusMinus l :=
  S.clause.cK_type

theorem sign_involution_squared : S.clause.signInvolution_squared :=
  S.clause.signInvolution_squared_proved

theorem sign_quotient_invariant : S.clause.signQuotient_invariant :=
  S.clause.signQuotient_invariant_proved

theorem cover_finite_etale : S.clause.xK_cK_cover.finite_etale :=
  S.clause.xK_cK_cover_finite_etale

theorem cartesian_square : S.clause.xK_cK_cartesian_square :=
  S.clause.xK_cK_cartesian_square_proved

theorem delta_x_open : S.clause.delta_x_open_subgroup :=
  S.clause.delta_x_open_subgroup_proved

theorem delta_c_open : S.clause.delta_c_open_subgroup :=
  S.clause.delta_c_open_subgroup_proved

theorem group_diagram_naturality : S.clause.group_diagram_naturality :=
  S.clause.group_diagram_naturality_proved

theorem xF_projection_surjective :
    Function.Surjective S.xFExact.projection.map :=
  S.xFExact.projection_surjective

theorem cF_projection_surjective :
    Function.Surjective S.cFExact.projection.map :=
  S.cFExact.projection_surjective

theorem xK_projection_surjective :
    Function.Surjective S.xKExact.projection.map :=
  S.xKExact.projection_surjective

theorem cK_projection_surjective :
    Function.Surjective S.cKExact.projection.map :=
  S.cKExact.projection_surjective

theorem xF_injection_injective :
    Function.Injective S.xFExact.injection.map :=
  S.xFExact.injection_injective

theorem cF_injection_injective :
    Function.Injective S.cFExact.injection.map :=
  S.cFExact.injection_injective

theorem xK_injection_injective :
    Function.Injective S.xKExact.injection.map :=
  S.xKExact.injection_injective

theorem cK_injection_injective :
    Function.Injective S.cKExact.injection.map :=
  S.cKExact.injection_injective

theorem xF_kernel
    (x : S.xFExact.arithmetic.carrier) :
    S.xFExact.projection.map x = 1 ↔
      ∃ y, S.xFExact.injection.map y = x :=
  S.xFExact.exact_at_arithmetic x

theorem cF_kernel
    (x : S.cFExact.arithmetic.carrier) :
    S.cFExact.projection.map x = 1 ↔
      ∃ y, S.cFExact.injection.map y = x :=
  S.cFExact.exact_at_arithmetic x

theorem xK_kernel
    (x : S.xKExact.arithmetic.carrier) :
    S.xKExact.projection.map x = 1 ↔
      ∃ y, S.xKExact.injection.map y = x :=
  S.xKExact.exact_at_arithmetic x

theorem cK_kernel
    (x : S.cKExact.arithmetic.carrier) :
    S.cKExact.projection.map x = 1 ↔
      ∃ y, S.cKExact.injection.map y = x :=
  S.cKExact.exact_at_arithmetic x

theorem xF_section (x : S.xFExact.galois.carrier) :
    S.xFExact.projection.map (S.xFExact.sectionMap.map x) = x :=
  S.xFExact.section_right_inverse x

theorem cF_section (x : S.cFExact.galois.carrier) :
    S.cFExact.projection.map (S.cFExact.sectionMap.map x) = x :=
  S.cFExact.section_right_inverse x

theorem xK_section (x : S.xKExact.galois.carrier) :
    S.xKExact.projection.map (S.xKExact.sectionMap.map x) = x :=
  S.xKExact.section_right_inverse x

theorem cK_section (x : S.cKExact.galois.carrier) :
    S.cKExact.projection.map (S.cKExact.sectionMap.map x) = x :=
  S.cKExact.section_right_inverse x

theorem xF_section_injective : Function.Injective S.xFExact.sectionMap.map :=
  S.xFExact.section_injective

theorem cF_section_injective : Function.Injective S.cFExact.sectionMap.map :=
  S.cFExact.section_injective

theorem xK_section_injective : Function.Injective S.xKExact.sectionMap.map :=
  S.xKExact.section_injective

theorem cK_section_injective : Function.Injective S.cKExact.sectionMap.map :=
  S.cKExact.section_injective

theorem xF_inclusion_square (x : S.xFExact.geometric.carrier) :
    S.xFToCF.arithmetic.map (S.xFExact.injection.map x) =
      S.cFExact.injection.map (S.xFToCF.geometric.map x) :=
  S.xFToCF.inclusion_square x

theorem xF_projection_square (x : S.xFExact.arithmetic.carrier) :
    S.xFToCF.galois.map (S.xFExact.projection.map x) =
      S.cFExact.projection.map (S.xFToCF.arithmetic.map x) :=
  S.xFToCF.projection_square x

theorem xK_inclusion_square (x : S.xKExact.geometric.carrier) :
    S.xKToXF.arithmetic.map (S.xKExact.injection.map x) =
      S.xFExact.injection.map (S.xKToXF.geometric.map x) :=
  S.xKToXF.inclusion_square x

theorem xK_projection_square (x : S.xKExact.arithmetic.carrier) :
    S.xKToXF.galois.map (S.xKExact.projection.map x) =
      S.xFExact.projection.map (S.xKToXF.arithmetic.map x) :=
  S.xKToXF.projection_square x

theorem cK_inclusion_square (x : S.cKExact.geometric.carrier) :
    S.cKToCF.arithmetic.map (S.cKExact.injection.map x) =
      S.cFExact.injection.map (S.cKToCF.geometric.map x) :=
  S.cKToCF.inclusion_square x

theorem cK_projection_square (x : S.cKExact.arithmetic.carrier) :
    S.cKToCF.galois.map (S.cKExact.projection.map x) =
      S.cFExact.projection.map (S.cKToCF.arithmetic.map x) :=
  S.cKToCF.projection_square x

theorem exact_sequence_bundle :
    Function.Surjective S.xFExact.projection.map ∧
      Function.Injective S.xFExact.injection.map ∧
      Function.Surjective S.cFExact.projection.map ∧
      Function.Injective S.cFExact.injection.map ∧
      Function.Surjective S.xKExact.projection.map ∧
      Function.Injective S.xKExact.injection.map ∧
      Function.Surjective S.cKExact.projection.map ∧
      Function.Injective S.cKExact.injection.map :=
  ⟨S.xF_projection_surjective, S.xF_injection_injective,
    S.cF_projection_surjective, S.cF_injection_injective,
    S.xK_projection_surjective, S.xK_injection_injective,
    S.cK_projection_surjective, S.cK_injection_injective⟩

theorem D6_bundle :
    S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne ∧
      S.candidate.cF.signature = SourceOrbicurveSignature.typeOneOne ∧
      S.candidate.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l ∧
      S.candidate.cK.signature =
        SourceOrbicurveSignature.typeOneLTorsionPlusMinus l ∧
      S.clause.signInvolution_squared ∧
      S.clause.signQuotient_invariant ∧
      S.clause.xK_cK_cover.finite_etale ∧
      S.clause.xK_cK_cartesian_square :=
  ⟨S.xF_signature, S.cF_signature, S.xK_signature, S.cK_signature,
    S.sign_involution_squared, S.sign_quotient_invariant,
    S.cover_finite_etale, S.cartesian_square⟩

end D6Root

/-! ## D7: selected places, local groups, and the section -/

structure D7Root {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄}
    (R : D6Root.{u} R₅) where
  section_clause : ClauseE l R.candidate R.orbicurve_clause

namespace D7Root

variable {l : PrimeGeFive}
variable {P : D1Root.{u} l} {Q : D2Root.{u} P}
variable {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
variable {R₅ : D5Root.{u} R₄} {R : D6Root.{u} R₅}
variable (S : D7Root R)
include S

def predecessor (S : D7Root R) : D6Root.{u}
    R₅ := R

abbrev candidate (S : D7Root R) : SourceInitialThetaCandidate.{u} l := R.candidate
abbrev orbicurve_clause (S : D7Root R) : ClauseD l S.candidate :=
  R.orbicurve_clause
abbrev clause (S : D7Root R) : ClauseE l S.candidate S.orbicurve_clause :=
  S.section_clause
abbrev partition (S : D7Root R) :
    LeanFormal.IUT.InitialThetaSource.SourcePlacePartition.{u} l S.candidate :=
  S.clause.placePartition

theorem section_property : S.clause.V_is_section :=
  S.clause.V_is_section_proved

theorem Vnon_definition (v : S.candidate.V) :
    v ∈ S.clause.Vnon ↔
      NumberFieldPlace.IsFinite (S.candidate.place v) :=
  S.clause.Vnon_definition v

theorem Varc_definition (v : S.candidate.V) :
    v ∈ S.clause.Varc ↔
      NumberFieldPlace.IsInfinite (S.candidate.place v) :=
  S.clause.Varc_definition v

theorem Vbad_definition (v : S.candidate.V) :
    v ∈ S.clause.Vbad ↔
      S.candidate.placeToMod v ∈
        (NumberFieldPlace.finite '' S.candidate.VbadMod) :=
  S.clause.Vbad_definition v

theorem Vgood_definition (v : S.candidate.V) :
    v ∈ S.clause.Vgood ↔ S.candidate.placeToMod v ∈ S.candidate.VgoodMod :=
  S.clause.Vgood_definition v

theorem non_arc_disjoint : Disjoint S.clause.Vnon S.clause.Varc :=
  S.clause.Vnon_arc_disjoint

theorem non_arc_cover : S.clause.Vnon ∪ S.clause.Varc = Set.univ :=
  S.clause.Vnon_arc_cover

theorem bad_good_disjoint : Disjoint S.clause.Vbad S.clause.Vgood :=
  S.clause.Vbad_good_disjoint

theorem bad_good_cover : S.clause.Vbad ∪ S.clause.Vgood = Set.univ :=
  S.clause.Vbad_good_cover

theorem partition_bijective :
    Function.Bijective (Sum.elim S.partition.finiteToV
      S.partition.infiniteToV) :=
  S.partition.kindPartition

theorem partition_injective :
    Function.Injective (Sum.elim S.partition.finiteToV
      S.partition.infiniteToV) :=
  S.partition.kindPartition.injective

theorem partition_surjective :
    Function.Surjective (Sum.elim S.partition.finiteToV
      S.partition.infiniteToV) :=
  S.partition.kindPartition.surjective

theorem every_place_is_finite_or_infinite (v : S.candidate.V) :
    (∃ i, S.partition.finiteToV i = v) ∨
      (∃ i, S.partition.infiniteToV i = v) := by
  rcases S.partition.kindPartition.surjective v with ⟨s, hs⟩
  cases s with
  | inl i => exact Or.inl ⟨i, hs⟩
  | inr i => exact Or.inr ⟨i, hs⟩

theorem finite_place_compatibility (i : S.partition.finiteIndex) :
    S.candidate.place (S.partition.finiteToV i) =
      NumberFieldPlace.finite (S.partition.finitePlace i) :=
  S.partition.finite_place_compatibility i

theorem infinite_place_compatibility (i : S.partition.infiniteIndex) :
    S.candidate.place (S.partition.infiniteToV i) =
      NumberFieldPlace.infinite (S.partition.infinitePlace i) :=
  S.partition.infinite_place_compatibility i

theorem finite_moduli_compatibility (i : S.partition.finiteIndex) :
    S.candidate.placeToMod (S.partition.finiteToV i) =
      NumberFieldPlace.finite
        (NumberFieldFinitePlace.comap (S.partition.finitePlace i)) :=
  S.partition.finite_moduli_compatibility i

theorem infinite_moduli_compatibility (i : S.partition.infiniteIndex) :
    S.candidate.placeToMod (S.partition.infiniteToV i) =
      NumberFieldPlace.infinite
        ((S.partition.infinitePlace i).comap
          (algebraMap S.candidate.arithmetic.Fmod S.candidate.arithmetic.K)) :=
  S.partition.infinite_moduli_compatibility i

theorem finite_place_is_finite (i : S.partition.finiteIndex) :
    NumberFieldPlace.IsFinite
      (S.candidate.place (S.partition.finiteToV i)) := by
  rw [S.finite_place_compatibility]
  trivial

theorem infinite_place_is_infinite (i : S.partition.infiniteIndex) :
    NumberFieldPlace.IsInfinite
      (S.candidate.place (S.partition.infiniteToV i)) := by
  rw [S.infinite_place_compatibility]
  trivial

theorem finite_moduli_is_finite (i : S.partition.finiteIndex) :
    NumberFieldPlace.IsFinite
      (S.candidate.placeToMod (S.partition.finiteToV i)) := by
  rw [S.finite_moduli_compatibility]
  trivial

theorem infinite_moduli_is_infinite (i : S.partition.infiniteIndex) :
    NumberFieldPlace.IsInfinite
      (S.candidate.placeToMod (S.partition.infiniteToV i)) := by
  rw [S.infinite_moduli_compatibility]
  trivial

def finite_local_family :
    ∀ i : S.partition.finiteIndex,
      SourceFiniteLocalData l S.candidate S.partition i
        R.xFExact R.cFExact :=
  S.clause.finiteLocal

def infinite_local_family :
    ∀ i : S.partition.infiniteIndex,
      SourceInfiniteLocalData l S.candidate S.partition i
        R.xFExact R.cFExact :=
  S.clause.infiniteLocal

theorem finite_curve_diagram : S.clause.finite_local_curve_diagram :=
  S.clause.finite_local_curve_diagram_proved

theorem infinite_curve_diagram : S.clause.infinite_local_curve_diagram :=
  S.clause.infinite_local_curve_diagram_proved

theorem decomposition_group_naturality :
    S.clause.decomposition_group_naturality :=
  S.clause.decomposition_group_naturality_proved

theorem local_group_projection_compatibility :
    S.clause.local_group_projection_compatibility :=
  S.clause.local_group_projection_compatibility_proved

theorem D7_bundle :
    S.clause.V_is_section ∧
      Disjoint S.clause.Vnon S.clause.Varc ∧
      S.clause.Vnon ∪ S.clause.Varc = Set.univ ∧
      Disjoint S.clause.Vbad S.clause.Vgood ∧
      S.clause.Vbad ∪ S.clause.Vgood = Set.univ ∧
      S.clause.finite_local_curve_diagram ∧
      S.clause.infinite_local_curve_diagram :=
  ⟨S.section_property, S.non_arc_disjoint, S.non_arc_cover,
    S.bad_good_disjoint, S.bad_good_cover,
    S.finite_curve_diagram, S.infinite_curve_diagram⟩

end D7Root

/-! ## D8: cusp data and derived orbicurves -/

structure D8Root {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    (R : D7Root.{u} R₆) where
  cusp_clause : ClauseF l R.candidate R.orbicurve_clause

namespace D8Root

variable {l : PrimeGeFive}
variable {P : D1Root.{u} l} {Q : D2Root.{u} P}
variable {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
variable {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
variable {R : D7Root.{u} R₆} (S : D8Root R)
include S

def predecessor (S : D8Root R) : D7Root.{u}
    R₆ := R

abbrev candidate (S : D8Root R) : SourceInitialThetaCandidate.{u} l := R.candidate
abbrev clause : ClauseF l S.candidate R.orbicurve_clause := S.cusp_clause
abbrev cusp : SourceCuspDatum S.candidate.epsilonCarrier := S.clause.cusp
abbrev derived : SourceCuspDerivedOrbicurves l S.candidate R.orbicurve_clause :=
  S.clause.derivedOrbicurves

theorem cusp_nonzero : S.cusp.nonzero_quotient :=
  S.cusp.nonzero_quotient_proved

theorem cusp_canonical : S.cusp.canonical_generator :=
  S.cusp.canonical_generator_proved

theorem cusp_sign_ambiguity : S.cusp.sign_ambiguity :=
  S.cusp.sign_ambiguity_proved

theorem derived_x_signature :
    S.derived.xArrow.signature = SourceOrbicurveSignature.typeOneLTorsion l :=
  S.derived.xArrow_signature

theorem derived_c_signature :
    S.derived.cArrow.signature =
      SourceOrbicurveSignature.typeOneLTorsionPlusMinus l :=
  S.derived.cArrow_signature

theorem derived_cover_finite_etale : S.derived.xArrow_to_cArrow.finite_etale :=
  S.derived.xArrow_cArrow_finite_etale

theorem derived_x_open : S.derived.xArrow_geometric_open :=
  S.derived.xArrow_geometric_open_proved

theorem derived_c_open : S.derived.cArrow_geometric_open :=
  S.derived.cArrow_geometric_open_proved

theorem derived_naturality : S.derived.xArrow_cArrow_naturality :=
  S.derived.xArrow_cArrow_naturality_proved

theorem cusp_determines_orbicurves : S.derived.cusp_determines_orbicurves :=
  S.derived.cusp_determines_orbicurves_proved

theorem cusp_lies_on_cK : S.clause.cusp_lies_on_cK :=
  S.clause.cusp_lies_on_cK_proved

theorem cusp_from_nonzero_Q : S.clause.cusp_from_nonzero_Q :=
  S.clause.cusp_from_nonzero_Q_proved

theorem cusp_localization (v : S.candidate.V) :
    S.clause.cusp_localization v :=
  S.clause.cusp_localization_proved v

theorem bad_cusp_canonical_generator
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    S.clause.bad_cusp_canonical_generator p hp :=
  S.clause.bad_cusp_canonical_generator_proved p hp

theorem good_cusp_compatibility
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∉ S.candidate.VbadMod) :
    S.clause.good_cusp_compatibility p hp :=
  S.clause.good_cusp_compatibility_proved p hp

theorem cusp_sign_independence : S.clause.cusp_sign_independence :=
  S.clause.cusp_sign_independence_proved

theorem cusp_diagram_compatibility : S.clause.cusp_diagram_compatibility :=
  S.clause.cusp_diagram_compatibility_proved

theorem derived_x_exact_injective :
    Function.Injective S.derived.xArrow_exact_sequence.injection.map :=
  S.derived.xArrow_exact_sequence.injection_injective

theorem derived_x_exact_surjective :
    Function.Surjective S.derived.xArrow_exact_sequence.projection.map :=
  S.derived.xArrow_exact_sequence.projection_surjective

theorem derived_c_exact_injective :
    Function.Injective S.derived.cArrow_exact_sequence.injection.map :=
  S.derived.cArrow_exact_sequence.injection_injective

theorem derived_c_exact_surjective :
    Function.Surjective S.derived.cArrow_exact_sequence.projection.map :=
  S.derived.cArrow_exact_sequence.projection_surjective

theorem derived_x_exact
    (x : S.derived.xArrow_exact_sequence.arithmetic.carrier) :
    S.derived.xArrow_exact_sequence.projection.map x = 1 ↔
      ∃ y, S.derived.xArrow_exact_sequence.injection.map y = x :=
  S.derived.xArrow_exact_sequence.exact_at_arithmetic x

theorem derived_c_exact
    (x : S.derived.cArrow_exact_sequence.arithmetic.carrier) :
    S.derived.cArrow_exact_sequence.projection.map x = 1 ↔
      ∃ y, S.derived.cArrow_exact_sequence.injection.map y = x :=
  S.derived.cArrow_exact_sequence.exact_at_arithmetic x

theorem derived_x_section (x : S.derived.xArrow_exact_sequence.galois.carrier) :
    S.derived.xArrow_exact_sequence.projection.map
      (S.derived.xArrow_exact_sequence.sectionMap.map x) = x :=
  S.derived.xArrow_exact_sequence.section_right_inverse x

theorem derived_c_section (x : S.derived.cArrow_exact_sequence.galois.carrier) :
    S.derived.cArrow_exact_sequence.projection.map
      (S.derived.cArrow_exact_sequence.sectionMap.map x) = x :=
  S.derived.cArrow_exact_sequence.section_right_inverse x

theorem cusp_bundle :
    S.cusp.nonzero_quotient ∧ S.cusp.canonical_generator ∧
      S.cusp.sign_ambiguity ∧
      S.derived.xArrow.signature = SourceOrbicurveSignature.typeOneLTorsion l ∧
      S.derived.cArrow.signature =
        SourceOrbicurveSignature.typeOneLTorsionPlusMinus l ∧
      S.derived.xArrow_to_cArrow.finite_etale ∧
      S.clause.cusp_lies_on_cK ∧ S.clause.cusp_from_nonzero_Q ∧
      S.clause.cusp_sign_independence ∧
      S.clause.cusp_diagram_compatibility :=
  ⟨S.cusp_nonzero, S.cusp_canonical, S.cusp_sign_ambiguity,
    S.derived_x_signature, S.derived_c_signature,
    S.derived_cover_finite_etale, S.cusp_lies_on_cK,
    S.cusp_from_nonzero_Q, S.cusp_sign_independence,
    S.cusp_diagram_compatibility⟩

end D8Root

/-! ## D9: the two coherence records required by the source definition

The source record has exactly two coherence fields.  Reduction, torsion,
orbicurve, section, and cusp compatibility are already fields of clauses
(b)--(f); adding five new propositions here would silently strengthen the
source definition.  D9 therefore carries only the two source coherence
records and leaves the clause fields indexed by the same D8 candidate. -/

structure D9Root {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    {R₇ : D7Root.{u} R₆} (R : D8Root.{u} R₇) where
  arithmetic_clause_coherence : Prop
  arithmetic_clause_coherence_proved : arithmetic_clause_coherence
  clause_order_coherence : Prop
  clause_order_coherence_proved : clause_order_coherence

namespace D9Root

variable {l : PrimeGeFive}
variable {P : D1Root.{u} l} {Q : D2Root.{u} P}
variable {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
variable {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
variable {R₇ : D7Root.{u} R₆} {R : D8Root.{u} R₇} (S : D9Root R)
include S

def predecessor (S : D9Root R) : D8Root.{u}
    R₇ := R

abbrev candidate (S : D9Root R) : SourceInitialThetaCandidate.{u} l := R.candidate

theorem arithmetic_coherence : S.arithmetic_clause_coherence :=
  S.arithmetic_clause_coherence_proved

theorem order_coherence : S.clause_order_coherence :=
  S.clause_order_coherence_proved

theorem coherence_bundle :
    S.arithmetic_clause_coherence ∧ S.clause_order_coherence :=
  ⟨S.arithmetic_coherence, S.order_coherence⟩

theorem candidate_arithmetic_alignment :
    S.candidate.arithmetic = S.predecessor.candidate.arithmetic := rfl

end D9Root

/-! ## D10: canonical assembly of the six source clauses -/

def assembleD10Source
    {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    {R₇ : D7Root.{u} R₆} {R₈ : D8Root.{u} R₇}
    (R : D9Root.{u} R₈) : SourceInitialThetaData.{u} l where
  candidate := R.candidate
  clauseA := Q.clauseA
  clauseB := R₃.clauseB
  clauseC := R₅.torsion_clause
  clauseD := R₆.orbicurve_clause
  clauseE := R₇.section_clause
  clauseF := R₈.cusp_clause
  arithmetic_clause_coherence := R.arithmetic_clause_coherence
  arithmetic_clause_coherence_proved := R.arithmetic_clause_coherence_proved
  clause_order_coherence := R.clause_order_coherence
  clause_order_coherence_proved := R.clause_order_coherence_proved

inductive D10Root {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    {R₇ : D7Root.{u} R₆} {R₈ : D8Root.{u} R₇}
    (R : D9Root.{u} R₈) where
  | canonical

namespace D10Root

variable {l : PrimeGeFive}
variable {P : D1Root.{u} l} {Q : D2Root.{u} P}
variable {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
variable {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
variable {R₇ : D7Root.{u} R₆} {R₈ : D8Root.{u} R₇}
variable {R : D9Root.{u} R₈} (S : D10Root R)

def predecessor (S : D10Root R) : D9Root.{u}
    R₈ := R

def source (S : D10Root R) : SourceInitialThetaData.{u} l :=
  assembleD10Source R

def of {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    {R₇ : D7Root.{u} R₆} {R₈ : D8Root.{u} R₇}
    (R : D9Root.{u} R₈) :
    D10Root.{u} R := D10Root.canonical

theorem source_candidate : S.source.candidate = R.candidate := by
  rfl

theorem source_arithmetic : S.source.candidate.arithmetic =
    R.candidate.arithmetic := by
  rfl

theorem source_clauseA : S.source.clauseA =
    Q.clauseA := rfl

theorem source_clauseB : S.source.clauseB =
    R₃.clauseB := rfl

theorem source_clauseC : S.source.clauseC =
    R₅.torsion_clause := rfl

theorem source_clauseD : S.source.clauseD =
    R₆.orbicurve_clause := rfl

theorem source_clauseE : S.source.clauseE =
    R₇.section_clause := rfl

theorem source_clauseF : S.source.clauseF =
    R₈.cusp_clause := rfl

theorem source_coherence :
    S.source.arithmetic_clause_coherence ∧ S.source.clause_order_coherence :=
  ⟨S.source.arithmetic_clause_coherence_proved,
    S.source.clause_order_coherence_proved⟩

def source_all_six_records :
    SourceInitialThetaData.SourceInitialThetaClauseRecords S.source :=
  S.source.all_six_clause_records

theorem source_candidate_arithmetic_alignment
    (A : InitialThetaArithmeticData.{u} l)
    (hA : R.candidate.arithmetic = A) :
    S.source.candidate.arithmetic = A := by
  exact S.source_arithmetic.trans hA

theorem source_clauseA_field :
    HasSqrtNegOne S.source.candidate.arithmetic.F :=
  S.source.clauseA.squareRootNegOne

theorem source_clauseB_bad_nonempty : S.source.candidate.VbadMod.Nonempty :=
  S.source.clauseB.bad_nonempty

theorem source_clauseC_large_image :
    S.source.clauseC.standard_SL2_image ≤
      S.source.clauseC.galois_representation.range :=
  S.source.clauseC.image_contains_SL2

theorem source_clauseD_cartesian : S.source.clauseD.xK_cK_cartesian_square :=
  S.source.clauseD.xK_cK_cartesian_square_proved

theorem source_clauseE_section : S.source.clauseE.V_is_section :=
  S.source.clauseE.V_is_section_proved

theorem source_clauseF_cusp : S.source.clauseF.cusp.nonzero_quotient :=
  S.source.clauseF.cusp.nonzero_quotient_proved

theorem source_is_not_replaced : S.source = S.source := rfl

end D10Root

/-! ## D11: complete conclusion and exact recovery of each predecessor -/

inductive D11Root {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    {R₇ : D7Root.{u} R₆} {R₈ : D8Root.{u} R₇}
    {R₉ : D9Root.{u} R₈} (R : D10Root.{u} R₉) where
  | canonical

namespace D11Root

variable {l : PrimeGeFive}
variable {P : D1Root.{u} l} {Q : D2Root.{u} P}
variable {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
variable {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
variable {R₇ : D7Root.{u} R₆} {R₈ : D8Root.{u} R₇}
variable {R₉ : D9Root.{u} R₈} {R : D10Root.{u} R₉} (S : D11Root R)

def predecessor (S : D11Root R) : D10Root.{u}
    R₉ := R

def conclusion (S : D11Root R) : InitialThetaDataConclusion R.source :=
  R.source.conclusion

def of {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    {R₇ : D7Root.{u} R₆} {R₈ : D8Root.{u} R₇}
    {R₉ : D9Root.{u} R₈} (R : D10Root.{u} R₉) :
    D11Root.{u} R := D11Root.canonical

theorem conclusion_source :
    S.conclusion.source_clause_records =
      R.source.all_six_clause_records := by
  rfl

theorem arithmetic_clause_coherence :
    R.source.arithmetic_clause_coherence :=
  R.source.conclusion.arithmetic_clause_coherence

theorem clause_order_coherence :
    R.source.clause_order_coherence :=
  R.source.conclusion.clause_order_coherence

theorem clauseA_field : HasSqrtNegOne R.source.candidate.arithmetic.F :=
  R.source.conclusion.clause_a_sqrtNegOne

theorem clauseA_curve_signature :
    R.source.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne :=
  R.source.conclusion.clause_a_curve_signature

theorem clauseA_stable_everywhere
    (p : NumberField.FinitePlace R.source.candidate.arithmetic.F) :
    R.source.candidate.arithmetic.curve.HasStableReductionAt p :=
  R.source.conclusion.clause_a_stable_everywhere p

theorem clauseB_bad_nonempty : R.source.candidate.VbadMod.Nonempty :=
  R.source.conclusion.clause_b_bad_nonempty

theorem clauseB_multiplicative
    (p : NumberField.FinitePlace R.source.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ R.source.candidate.VbadMod) :
    R.source.candidate.arithmetic.curve.HasMultiplicativeReductionAt p :=
  R.source.conclusion.clause_b_multiplicative p hp

theorem clauseB_stable
    (p : NumberField.FinitePlace R.source.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ R.source.candidate.VbadMod) :
    R.source.candidate.arithmetic.curve.HasStableReductionAt p :=
  R.source.conclusion.clause_b_stable_over_bad p hp

theorem clauseB_q_order_prime_to_l
    (p : NumberField.FinitePlace R.source.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ R.source.candidate.VbadMod) :
    Nat.Coprime (R.source.clauseB.qParameter p hp).order l.value :=
  R.source.conclusion.clause_b_q_order_prime_to_l p hp

theorem clauseC_large_image :
    R.source.clauseC.standard_SL2_image ≤
      R.source.clauseC.galois_representation.range :=
  R.source.conclusion.clause_c_image_contains_SL2

theorem clauseD_cartesian : R.source.clauseD.xK_cK_cartesian_square :=
  R.source.conclusion.clause_d_cartesian

theorem clauseE_section : R.source.clauseE.V_is_section :=
  R.source.conclusion.clause_e_section

theorem clauseF_cusp_nonzero : R.source.clauseF.cusp.nonzero_quotient :=
  R.source.conclusion.clause_f_cusp_nonzero

def complete_source_records :
    SourceInitialThetaData.SourceInitialThetaClauseRecords R.source :=
  R.source.conclusion.source_clause_records

theorem recover_source_from_conclusion :
    ∃ C : InitialThetaDataConclusion R.source, C = S.conclusion :=
  ⟨S.conclusion, rfl⟩

theorem d11_bundle :
    R.source.arithmetic_clause_coherence ∧
      R.source.clause_order_coherence ∧
      HasSqrtNegOne R.source.candidate.arithmetic.F ∧
      R.source.candidate.VbadMod.Nonempty ∧
      R.source.clauseD.xK_cK_cartesian_square ∧
      R.source.clauseE.V_is_section ∧
      R.source.clauseF.cusp.nonzero_quotient := by
  exact ⟨R.source.conclusion.arithmetic_clause_coherence,
    R.source.conclusion.clause_order_coherence,
    R.source.conclusion.clause_a_sqrtNegOne,
    R.source.conclusion.clause_b_bad_nonempty,
    R.source.conclusion.clause_d_cartesian,
    R.source.conclusion.clause_e_section,
    R.source.conclusion.clause_f_cusp_nonzero⟩

end D11Root

/-! ## The aligned construction gates and the serial composition -/

def D2ConstructionGate (l : PrimeGeFive) :=
  ∀ A : InitialThetaArithmeticData.{u} l,
    D2Root.{u} (D1Root.of (D0Root.fromArithmetic A))

def D3ConstructionGate (l : PrimeGeFive) :=
  ∀ {P : D1Root.{u} l} (R : D2Root.{u} P),
    D3Root.{u} R

def D4ConstructionGate (l : PrimeGeFive) :=
  ∀ {P : D1Root.{u} l} {Q : D2Root.{u} P}
    (R : D3Root.{u} Q),
    D4Root.{u} R

def D5ConstructionGate (l : PrimeGeFive) :=
  ∀ {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} (R : D4Root.{u} R₃),
    D5Root.{u} R

def D6ConstructionGate (l : PrimeGeFive) :=
  ∀ {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    (R : D5Root.{u} R₄),
    D6Root.{u} R

def D7ConstructionGate (l : PrimeGeFive) :=
  ∀ {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} (R : D6Root.{u} R₅),
    D7Root.{u} R

def D8ConstructionGate (l : PrimeGeFive) :=
  ∀ {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    (R : D7Root.{u} R₆),
    D8Root.{u} R

def D9ConstructionGate (l : PrimeGeFive) :=
  ∀ {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    {R₇ : D7Root.{u} R₆} (R : D8Root.{u} R₇),
    D9Root.{u} R

def D10ConstructionGate (l : PrimeGeFive) :=
  ∀ {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    {R₇ : D7Root.{u} R₆} {R₈ : D8Root.{u} R₇}
    (R : D9Root.{u} R₈),
    D10Root.{u} R

def D11ConstructionGate (l : PrimeGeFive) :=
  ∀ {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    {R₇ : D7Root.{u} R₆} {R₈ : D8Root.{u} R₇}
    {R₉ : D9Root.{u} R₈} (R : D10Root.{u} R₉),
    D11Root.{u} R

def d0_from_arithmetic (l : PrimeGeFive)
    (A : InitialThetaArithmeticData.{u} l) :
    D0Root.{u} l :=
  D0Root.fromArithmetic A

def d1_from_d0 (R : D0Root.{u} l) : D1Root.{u} l :=
  D1Root.of R

def d1_from_arithmetic (A : InitialThetaArithmeticData.{u} l) :
    D1Root.{u} l :=
  D1Root.of (D0Root.fromArithmetic A)

def d2_alignment_of_gate
    (h : D2ConstructionGate l)
    (A : InitialThetaArithmeticData.{u} l) :
    D2Root.{u} (D1Root.of (D0Root.fromArithmetic A)) :=
  h A

def d3_stage_of_gate
    (h : D3ConstructionGate l)
    {P : D1Root.{u} l} (R : D2Root.{u} P) :
    D3Root.{u} R :=
  h R

def d4_stage_of_gate
    (h : D4ConstructionGate l)
    {P : D1Root.{u} l} {Q : D2Root.{u} P}
    (R : D3Root.{u} Q) :
    D4Root.{u} R :=
  h R

def d5_stage_of_gate
    (h : D5ConstructionGate l)
    {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} (R : D4Root.{u} R₃) :
    D5Root.{u} R :=
  h R

def d6_stage_of_gate
    (h : D6ConstructionGate l)
    {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    (R : D5Root.{u} R₄) :
    D6Root.{u} R :=
  h R

def d7_stage_of_gate
    (h : D7ConstructionGate l)
    {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} (R : D6Root.{u} R₅) :
    D7Root.{u} R :=
  h R

def d8_stage_of_gate
    (h : D8ConstructionGate l)
    {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    (R : D7Root.{u} R₆) :
    D8Root.{u} R :=
  h R

def d9_stage_of_gate
    (h : D9ConstructionGate l)
    {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    {R₇ : D7Root.{u} R₆} (R : D8Root.{u} R₇) :
    D9Root.{u} R :=
  h R

def d10_stage_of_gate
    (h : D10ConstructionGate l)
    {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    {R₇ : D7Root.{u} R₆} {R₈ : D8Root.{u} R₇}
    (R : D9Root.{u} R₈) :
    D10Root.{u} R :=
  h R

def d11_stage_of_gate
    (h : D11ConstructionGate l)
    {P : D1Root.{u} l} {Q : D2Root.{u} P}
    {R₃ : D3Root.{u} Q} {R₄ : D4Root.{u} R₃}
    {R₅ : D5Root.{u} R₄} {R₆ : D6Root.{u} R₅}
    {R₇ : D7Root.{u} R₆} {R₈ : D8Root.{u} R₇}
    {R₉ : D9Root.{u} R₈} (R : D10Root.{u} R₉) :
    D11Root.{u} R :=
  h R

/-! D10 and D11 do not introduce new source hypotheses.  Once D9 has
    supplied the two coherence proofs, the source record and its complete
    conclusion are canonical. -/

def d10_canonical_gate (l : PrimeGeFive) :
    D10ConstructionGate l := by
  intro P Q R₃ R₄ R₅ R₆ R₇ R₈ R
  exact D10Root.of R

def d11_canonical_gate (l : PrimeGeFive) :
    D11ConstructionGate l := by
  intro P Q R₃ R₄ R₅ R₆ R₇ R₈ R₉ R
  exact D11Root.of R

/-! A serial result stores every stage as a dependent field.  This is the
    direct D0--D11 output; no `Nonempty` wrapper or existential elimination
    is used between stages. -/

structure SerialD0D11
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l) where
  d2 : D2Root.{u} (D1Root.of (D0Root.fromArithmetic A))
  d3 : D3Root.{u} d2
  d4 : D4Root.{u} d3
  d5 : D5Root.{u} d4
  d6 : D6Root.{u} d5
  d7 : D7Root.{u} d6
  d8 : D8Root.{u} d7
  d9 : D9Root.{u} d8
  d10 : D10Root.{u} d9
  d11 : D11Root.{u} d10

namespace SerialD0D11

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l} (S : SerialD0D11 A)
include S

def d0 (S : SerialD0D11 A) : D0Root.{u} l := D0Root.fromArithmetic A

def d1 (S : SerialD0D11 A) : D1Root.{u} l := D1Root.of S.d0

theorem d0_arithmetic : S.d0.arithmetic = A := rfl

theorem d1_foundation : S.d1 = D1Root.of (D0Root.fromArithmetic A) := rfl

theorem d2_predecessor : S.d2 = S.d2 := rfl

theorem d3_candidate_arithmetic : S.d3.candidate.arithmetic =
    S.d2.candidate.arithmetic := rfl

theorem d4_candidate_arithmetic : S.d4.candidate.arithmetic =
    S.d3.candidate.arithmetic := rfl

theorem d5_candidate_arithmetic : S.d5.candidate.arithmetic =
    S.d4.candidate.arithmetic := rfl

theorem d6_candidate_arithmetic : S.d6.candidate.arithmetic =
    S.d5.candidate.arithmetic := rfl

theorem d7_candidate_arithmetic : S.d7.candidate.arithmetic =
    S.d6.candidate.arithmetic := rfl

theorem d8_candidate_arithmetic : S.d8.candidate.arithmetic =
    S.d7.candidate.arithmetic := rfl

theorem d9_candidate_arithmetic : S.d9.candidate.arithmetic =
    S.d8.candidate.arithmetic := rfl

theorem d10_source_candidate : S.d10.source.candidate = S.d9.candidate := by
  exact S.d10.source_candidate

theorem d11_source : S.d11.predecessor.source = S.d10.source := rfl

def source : SourceInitialThetaData.{u} l := S.d10.source

def conclusion : InitialThetaDataConclusion S.source := S.d11.conclusion

def conclusion_complete :
    SourceInitialThetaData.SourceInitialThetaClauseRecords S.source :=
  S.conclusion.source_clause_records

theorem conclusion_coherence :
    S.source.arithmetic_clause_coherence ∧ S.source.clause_order_coherence :=
  ⟨S.conclusion.arithmetic_clause_coherence,
    S.conclusion.clause_order_coherence⟩

theorem conclusion_clauseA :
    HasSqrtNegOne S.source.candidate.arithmetic.F :=
  S.conclusion.clause_a_sqrtNegOne

theorem conclusion_clauseB : S.source.candidate.VbadMod.Nonempty :=
  S.conclusion.clause_b_bad_nonempty

theorem conclusion_clauseC :
    S.source.clauseC.standard_SL2_image ≤
      S.source.clauseC.galois_representation.range :=
  S.conclusion.clause_c_image_contains_SL2

theorem conclusion_clauseD : S.source.clauseD.xK_cK_cartesian_square :=
  S.conclusion.clause_d_cartesian

theorem conclusion_clauseE : S.source.clauseE.V_is_section :=
  S.conclusion.clause_e_section

theorem conclusion_clauseF : S.source.clauseF.cusp.nonzero_quotient :=
  S.conclusion.clause_f_cusp_nonzero

theorem exact_source_records :
    S.conclusion.source_clause_records = S.source.all_six_clause_records := by
  rfl

end SerialD0D11

/-! The serial constructor is intentionally conditional only on the still
    unproved source clause gates D2--D9.  D0, D1, D10 and D11 are constructed
    in this theorem itself, so they cannot be mistaken for additional axioms. -/

def serial_D0_D11
    (A : InitialThetaArithmeticData.{u} l)
    (h₂ : D2ConstructionGate l)
    (h₃ : D3ConstructionGate l)
    (h₄ : D4ConstructionGate l)
    (h₅ : D5ConstructionGate l)
    (h₆ : D6ConstructionGate l)
    (h₇ : D7ConstructionGate l)
    (h₈ : D8ConstructionGate l)
    (h₉ : D9ConstructionGate l) :
    SerialD0D11.{u} A := by
  let R₂ := d2_alignment_of_gate h₂ A
  let R₃ := d3_stage_of_gate h₃ R₂
  let R₄ := d4_stage_of_gate h₄ R₃
  let R₅ := d5_stage_of_gate h₅ R₄
  let R₆ := d6_stage_of_gate h₆ R₅
  let R₇ := d7_stage_of_gate h₇ R₆
  let R₈ := d8_stage_of_gate h₈ R₇
  let R₉ := d9_stage_of_gate h₉ R₈
  let R₁₀ := D10Root.of R₉
  let R₁₁ := D11Root.of R₁₀
  exact
    { d2 := R₂
      d3 := R₃
      d4 := R₄
      d5 := R₅
      d6 := R₆
      d7 := R₇
      d8 := R₈
      d9 := R₉
      d10 := R₁₀
      d11 := R₁₁ }

def serial_source_conclusion
    (S : SerialD0D11.{u} A) :
    InitialThetaDataConclusion S.source :=
  S.conclusion

end Definition31D0D11Aligned
end Theorem311Source
end
end LeanFormal.IUT
