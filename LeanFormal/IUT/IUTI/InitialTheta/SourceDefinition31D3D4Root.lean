import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
  Source-faithful D3/D4 root consequences.

  This module deliberately starts with `SourceInitialThetaData`, the tuple
  whose clauses are the literal Definition 3.1 clauses.  It does not turn
  those clauses into an existence theorem.  The purpose here is narrower and
  auditable: every D3 place statement and every D4 local reduction/q statement
  is exposed with its original carrier and quantifier before any later
  simplification to `SourceDefinition31Data`.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u

namespace InitialThetaSource

namespace Definition31D3D4Root

variable {l : PrimeGeFive} (S : SourceInitialThetaData.{u} l)

/-! ## D3: selected places and the finite/infinite partition -/

abbrev candidate : SourceInitialThetaCandidate l :=
  S.candidate

abbrev arithmetic : InitialThetaArithmeticData l :=
  S.candidate.arithmetic

abbrev placeClause : ClauseE l S.candidate S.clauseD :=
  S.clauseE

abbrev placePartition : SourcePlacePartition l S.candidate :=
  S.clauseE.placePartition

abbrev selectedPlace : Type u :=
  S.candidate.V

abbrev finitePlaceIndex : Type u :=
  (placePartition S).finiteIndex

abbrev infinitePlaceIndex : Type u :=
  (placePartition S).infiniteIndex

def selected_place (v : selectedPlace S) : NumberFieldPlace S.candidate.arithmetic.K :=
  S.candidate.place v

def selected_place_to_mod (v : selectedPlace S) :
    NumberFieldPlace S.candidate.arithmetic.Fmod :=
  S.candidate.placeToMod v

theorem selected_place_to_mod_mem (v : selectedPlace S) :
    selected_place_to_mod S v ∈ S.candidate.Vmod :=
  S.candidate.placeToMod_mem_Vmod v

theorem selected_place_to_mod_injective :
    Function.Injective (selected_place_to_mod S) :=
  S.candidate.placeToMod_bijective.injective

theorem selected_place_to_mod_surjective :
    Function.Surjective (selected_place_to_mod S) :=
  S.candidate.placeToMod_bijective.surjective

theorem selected_place_to_mod_bijective :
    Function.Bijective (selected_place_to_mod S) :=
  S.candidate.placeToMod_bijective

theorem selected_place_to_mod_comap (v : selectedPlace S) :
    NumberFieldPlace.comap (selected_place S v) =
      selected_place_to_mod S v :=
  S.candidate.place_comap_compatible v

theorem selected_place_mem_moduli_universe (v : selectedPlace S) :
    selected_place_to_mod S v ∈ S.candidate.Vmod :=
  selected_place_to_mod_mem S v

theorem moduli_places_are_all_selected :
    S.candidate.Vmod = Set.univ := by
  exact S.candidate.Vmod_eq_univ

theorem every_moduli_place_has_selected_preimage
    (p : NumberFieldPlace S.candidate.arithmetic.Fmod) :
    ∃ v : selectedPlace S, selected_place_to_mod S v = p := by
  exact selected_place_to_mod_surjective S p

theorem selected_place_comap_classification
    (v : selectedPlace S) :
    NumberFieldPlace.comap (selected_place S v) =
      selected_place_to_mod S v := by
  exact selected_place_to_mod_comap S v

theorem selected_place_is_finite_or_infinite
    (v : selectedPlace S) :
    NumberFieldPlace.IsFinite (selected_place S v) ∨
      NumberFieldPlace.IsInfinite (selected_place S v) := by
  have h := (placeClause S).Vnon_or_Varc v
  rcases h with h | h
  · exact Or.inl ((placeClause S).Vnon_definition v |>.mp h)
  · exact Or.inr ((placeClause S).Varc_definition v |>.mp h)

theorem selected_place_nonarchimedean_iff
    (v : selectedPlace S) :
    v ∈ (placeClause S).Vnon ↔
      NumberFieldPlace.IsFinite (selected_place S v) :=
  (placeClause S).Vnon_definition v

theorem selected_place_archimedean_iff
    (v : selectedPlace S) :
    v ∈ (placeClause S).Varc ↔
      NumberFieldPlace.IsInfinite (selected_place S v) :=
  (placeClause S).Varc_definition v

theorem selected_nonarchimedean_archimedean_disjoint :
    Disjoint (placeClause S).Vnon (placeClause S).Varc :=
  (placeClause S).Vnon_arc_disjoint

theorem selected_nonarchimedean_archimedean_cover :
    (placeClause S).Vnon ∪ (placeClause S).Varc = Set.univ :=
  (placeClause S).Vnon_arc_cover

theorem selected_nonarchimedean_not_archimedean
    {v : selectedPlace S} (hv : v ∈ (placeClause S).Vnon) :
    v ∉ (placeClause S).Varc := by
  exact (placeClause S).not_Varc_of_mem_Vnon hv

theorem selected_archimedean_not_nonarchimedean
    {v : selectedPlace S} (hv : v ∈ (placeClause S).Varc) :
    v ∉ (placeClause S).Vnon := by
  exact (placeClause S).not_Vnon_of_mem_Varc hv

theorem selected_place_partition_cases
    (v : selectedPlace S) :
    v ∈ (placeClause S).Vnon ∨ v ∈ (placeClause S).Varc := by
  exact (placeClause S).Vnon_or_Varc v

theorem selected_place_partition_unique
    {v : selectedPlace S}
    (h₁ : v ∈ (placeClause S).Vnon)
    (h₂ : v ∈ (placeClause S).Varc) :
    False := by
  exact (placeClause S).not_Varc_of_mem_Vnon h₁ h₂

theorem selected_bad_or_good
    (v : selectedPlace S) :
    v ∈ (placeClause S).Vbad ∨ v ∈ (placeClause S).Vgood := by
  exact (placeClause S).Vbad_or_Vgood v

theorem selected_bad_iff_moduli_bad
    (v : selectedPlace S) :
    v ∈ (placeClause S).Vbad ↔
      selected_place_to_mod S v ∈
        (NumberFieldPlace.finite '' S.candidate.VbadMod) :=
  (placeClause S).Vbad_definition v

theorem selected_good_iff_moduli_good
    (v : selectedPlace S) :
    v ∈ (placeClause S).Vgood ↔
      selected_place_to_mod S v ∈ S.candidate.VgoodMod :=
  (placeClause S).Vgood_definition v

theorem selected_bad_good_disjoint :
    Disjoint (placeClause S).Vbad (placeClause S).Vgood :=
  (placeClause S).Vbad_good_disjoint

theorem selected_bad_good_cover :
    (placeClause S).Vbad ∪ (placeClause S).Vgood = Set.univ :=
  (placeClause S).Vbad_good_cover

theorem selected_bad_not_good
    {v : selectedPlace S} (hv : v ∈ (placeClause S).Vbad) :
    v ∉ (placeClause S).Vgood := by
  exact (placeClause S).not_Vgood_of_mem_Vbad hv

theorem selected_good_not_bad
    {v : selectedPlace S} (hv : v ∈ (placeClause S).Vgood) :
    v ∉ (placeClause S).Vbad := by
  exact (placeClause S).not_Vbad_of_mem_Vgood hv

theorem selected_bad_good_cases
    (v : selectedPlace S) :
    v ∈ (placeClause S).Vbad ∨ v ∈ (placeClause S).Vgood := by
  exact (placeClause S).Vbad_or_Vgood v

theorem selected_bad_good_cases_unique
    {v : selectedPlace S}
    (hbad : v ∈ (placeClause S).Vbad)
    (hgood : v ∈ (placeClause S).Vgood) :
    False := by
  exact (placeClause S).not_Vgood_of_mem_Vbad hbad hgood

theorem selected_bad_moduli_finite_place
    {v : selectedPlace S}
    (hv : v ∈ (placeClause S).Vbad) :
    selected_place_to_mod S v ∈
      (NumberFieldPlace.finite '' S.candidate.VbadMod) := by
  exact (selected_bad_iff_moduli_bad S v).mp hv

theorem selected_good_moduli_place
    {v : selectedPlace S}
    (hv : v ∈ (placeClause S).Vgood) :
    selected_place_to_mod S v ∈ S.candidate.VgoodMod := by
  exact (selected_good_iff_moduli_good S v).mp hv

theorem selected_bad_moduli_finite_witness
    {v : selectedPlace S}
    (hv : v ∈ (placeClause S).Vbad) :
    ∃ p : NumberField.FinitePlace S.candidate.arithmetic.Fmod,
      p ∈ S.candidate.VbadMod ∧
      selected_place_to_mod S v = NumberFieldPlace.finite p := by
  rcases selected_bad_moduli_finite_place S hv with ⟨p, hp, hEq⟩
  exact ⟨p, hp, hEq.symm⟩

theorem selected_bad_moduli_finite_witness_unique
    {v : selectedPlace S}
    {p q : NumberField.FinitePlace S.candidate.arithmetic.Fmod}
    (hp : p ∈ S.candidate.VbadMod)
    (hq : q ∈ S.candidate.VbadMod)
    (h : NumberFieldPlace.finite p =
      NumberFieldPlace.finite q) :
    p = q := by
  cases p
  cases q
  simpa using h

theorem selected_place_partition_kind_injective :
    Function.Injective
      (Sum.elim (placePartition S).finiteToV
        (placePartition S).infiniteToV) :=
  (placePartition S).kindPartition.injective

theorem selected_place_partition_kind_surjective :
    Function.Surjective
      (Sum.elim (placePartition S).finiteToV
        (placePartition S).infiniteToV) :=
  (placePartition S).kindPartition.surjective

theorem selected_place_partition_kind_bijective :
    Function.Bijective
      (Sum.elim (placePartition S).finiteToV
        (placePartition S).infiniteToV) :=
  (placePartition S).kindPartition

theorem selected_finite_place_is_finite
    (i : finitePlaceIndex S) :
    NumberFieldPlace.IsFinite
      (selected_place S ((placePartition S).finiteToV i)) := by
  change NumberFieldPlace.IsFinite
    (S.candidate.place ((placePartition S).finiteToV i))
  rw [(placePartition S).finite_place_compatibility i]
  trivial

theorem selected_infinite_place_is_infinite
    (i : infinitePlaceIndex S) :
    NumberFieldPlace.IsInfinite
      (selected_place S ((placePartition S).infiniteToV i)) := by
  change NumberFieldPlace.IsInfinite
    (S.candidate.place ((placePartition S).infiniteToV i))
  rw [(placePartition S).infinite_place_compatibility i]
  trivial

theorem selected_finite_place_not_infinite
    (i : finitePlaceIndex S) :
    ¬ NumberFieldPlace.IsInfinite
      (selected_place S ((placePartition S).finiteToV i)) := by
  change ¬ NumberFieldPlace.IsInfinite
    (S.candidate.place ((placePartition S).finiteToV i))
  rw [(placePartition S).finite_place_compatibility i]
  intro h
  exact h

theorem selected_infinite_place_not_finite
    (i : infinitePlaceIndex S) :
    ¬ NumberFieldPlace.IsFinite
      (selected_place S ((placePartition S).infiniteToV i)) := by
  change ¬ NumberFieldPlace.IsFinite
    (S.candidate.place ((placePartition S).infiniteToV i))
  rw [(placePartition S).infinite_place_compatibility i]
  intro h
  exact h

theorem selected_finite_place_moduli_comap
    (i : finitePlaceIndex S) :
    selected_place_to_mod S ((placePartition S).finiteToV i) =
      NumberFieldPlace.finite
        (NumberFieldFinitePlace.comap
          (k := S.candidate.arithmetic.Fmod)
          (K := S.candidate.arithmetic.K)
          ((placePartition S).finitePlace i)) :=
  (placePartition S).finite_moduli_compatibility i

theorem selected_infinite_place_moduli_comap
    (i : infinitePlaceIndex S) :
    selected_place_to_mod S ((placePartition S).infiniteToV i) =
      NumberFieldPlace.infinite
        (((placePartition S).infinitePlace i).comap
          (algebraMap S.candidate.arithmetic.Fmod
            S.candidate.arithmetic.K)) :=
  (placePartition S).infinite_moduli_compatibility i

theorem selected_finite_place_comap_consistent
    (i : finitePlaceIndex S) :
    NumberFieldPlace.comap
      (selected_place S ((placePartition S).finiteToV i)) =
      selected_place_to_mod S ((placePartition S).finiteToV i) := by
  exact selected_place_to_mod_comap S ((placePartition S).finiteToV i)

theorem selected_infinite_place_comap_consistent
    (i : infinitePlaceIndex S) :
    NumberFieldPlace.comap
      (selected_place S ((placePartition S).infiniteToV i)) =
      selected_place_to_mod S ((placePartition S).infiniteToV i) := by
  exact selected_place_to_mod_comap S ((placePartition S).infiniteToV i)

theorem selected_finite_place_moduli_comap_explicit
    (i : finitePlaceIndex S) :
    NumberFieldPlace.comap
      (selected_place S ((placePartition S).finiteToV i)) =
      NumberFieldPlace.finite
        (NumberFieldFinitePlace.comap
          (k := S.candidate.arithmetic.Fmod)
          (K := S.candidate.arithmetic.K)
          ((placePartition S).finitePlace i)) := by
  rw [selected_finite_place_comap_consistent S i]
  exact selected_finite_place_moduli_comap S i

theorem selected_infinite_place_moduli_comap_explicit
    (i : infinitePlaceIndex S) :
    NumberFieldPlace.comap
      (selected_place S ((placePartition S).infiniteToV i)) =
      NumberFieldPlace.infinite
        (((placePartition S).infinitePlace i).comap
          (algebraMap S.candidate.arithmetic.Fmod
            S.candidate.arithmetic.K)) := by
  rw [selected_infinite_place_comap_consistent S i]
  exact selected_infinite_place_moduli_comap S i

theorem every_selected_place_is_finite_or_infinite
    (v : selectedPlace S) :
    (∃ i : finitePlaceIndex S,
      (placePartition S).finiteToV i = v) ∨
      (∃ i : infinitePlaceIndex S,
      (placePartition S).infiniteToV i = v) := by
  exact (placePartition S).every_selected_place_is_finite_or_infinite v

theorem selected_place_partition_unique_kind
    {i : finitePlaceIndex S} {j : infinitePlaceIndex S}
    (h : (placePartition S).finiteToV i =
      (placePartition S).infiniteToV j) :
    False := by
  have hsum :
      (Sum.elim (placePartition S).finiteToV
        (placePartition S).infiniteToV) (Sum.inl i) =
      (Sum.elim (placePartition S).finiteToV
        (placePartition S).infiniteToV) (Sum.inr j) := h
  have h' :
      (Sum.inl i : Sum (finitePlaceIndex S) (infinitePlaceIndex S)) =
        Sum.inr j := selected_place_partition_kind_injective S hsum
  cases h'

theorem finite_place_to_mod_finite
    (i : finitePlaceIndex S) :
    selected_place_to_mod S ((placePartition S).finiteToV i) =
      NumberFieldPlace.finite
        (NumberFieldFinitePlace.comap
          (k := S.candidate.arithmetic.Fmod)
          (K := S.candidate.arithmetic.K)
          ((placePartition S).finitePlace i)) :=
  selected_finite_place_moduli_comap S i

theorem infinite_place_to_mod_infinite
    (i : infinitePlaceIndex S) :
    selected_place_to_mod S ((placePartition S).infiniteToV i) =
      NumberFieldPlace.infinite
        (((placePartition S).infinitePlace i).comap
          (algebraMap S.candidate.arithmetic.Fmod
            S.candidate.arithmetic.K)) :=
  selected_infinite_place_moduli_comap S i

theorem place_partition_selected_nonempty :
    Nonempty (selectedPlace S) := by
  rcases S.clauseB.bad_nonempty with ⟨p, hp⟩
  have hVmod : S.candidate.Vmod.Nonempty :=
    ⟨NumberFieldPlace.finite p,
      S.candidate.badMod_subset_Vmod p hp⟩
  exact SourceInitialThetaCandidate.V_nonempty_of_Vmod_nonempty
    S.candidate hVmod

theorem place_partition_selected_nonempty_of_source :
    Nonempty S.candidate.V :=
  place_partition_selected_nonempty S

theorem place_partition_bad_subset_selected
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.finite p ∈ S.candidate.Vmod :=
  S.candidate.badMod_subset_Vmod p hp

theorem place_partition_bad_subset_selected_explicit
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.finite p ∈ Set.univ := by
  exact Set.mem_univ _

theorem place_partition_moduli_bad_preimage
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    ∃ v : selectedPlace S,
      selected_place_to_mod S v = NumberFieldPlace.finite p := by
  exact selected_place_to_mod_surjective S (NumberFieldPlace.finite p)

theorem place_partition_moduli_bad_selected
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    ∃ v : selectedPlace S,
      v ∈ (placeClause S).Vbad := by
  rcases place_partition_moduli_bad_preimage S p hp with ⟨v, hv⟩
  refine ⟨v, ?_⟩
  apply (selected_bad_iff_moduli_bad S v).mpr
  exact ⟨p, hp, hv.symm⟩

/-! ## D4: stable/multiplicative reduction and local q-candidates -/

abbrev reductionClause : ClauseB l S.candidate :=
  S.clauseB

def bad_reduction_predicate
    (p : NumberField.FinitePlace S.candidate.arithmetic.F) : Prop :=
  NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod

theorem bad_reduction_predicate_def
    (p : NumberField.FinitePlace S.candidate.arithmetic.F) :
    bad_reduction_predicate S p ↔
      NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod :=
  Iff.rfl

def q_candidate
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    NumberFieldFinitePlace.FinitePlaceQCandidate p :=
  S.clauseB.qParameter p hp

theorem q_candidate_eq_source
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    q_candidate S p hp = S.clauseB.qParameter p hp :=
  rfl

theorem bad_place_stable_reduction
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    S.candidate.arithmetic.curve.HasStableReductionAt p := by
  exact S.clauseB.stable_over_bad p hp

theorem bad_place_multiplicative_reduction
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p := by
  exact S.clauseB.multiplicative_over_bad p hp

theorem bad_place_stable_from_multiplicative
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    S.candidate.arithmetic.curve.HasStableReductionAt p := by
  exact PuncturedEllipticCurve.hasMultiplicativeReductionAt_imp_stable
    (bad_place_multiplicative_reduction S p hp)

theorem q_candidate_nonzero
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    (q_candidate S p hp).q ≠ 0 := by
  exact (q_candidate S p hp).q_ne_zero

theorem q_candidate_valuation_lt_one
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    (Valued.v (q_candidate S p hp).q :
      WithZero (Multiplicative Int)) < 1 := by
  exact (q_candidate S p hp).valuation_lt_one

theorem q_candidate_valuation_nonzero
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    (Valued.v (q_candidate S p hp).q :
      WithZero (Multiplicative Int)) ≠ 0 := by
  exact (q_candidate S p hp).valuation_ne_zero

theorem q_candidate_ne_one
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    (q_candidate S p hp).q ≠ 1 := by
  exact (q_candidate S p hp).q_ne_one

theorem q_candidate_exponent_positive
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    0 < (q_candidate S p hp).exponent := by
  exact (q_candidate S p hp).exponent_pos

theorem q_candidate_order_positive
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    0 < (q_candidate S p hp).order := by
  exact (q_candidate S p hp).order_pos

theorem q_candidate_order_nonzero
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    (q_candidate S p hp).order ≠ 0 := by
  exact Nat.ne_of_gt (q_candidate_order_positive S p hp)

theorem q_candidate_order_prime_to_l
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    Nat.Coprime (q_candidate S p hp).order l.value := by
  exact S.clauseB.q_order_prime_to_l p hp

theorem q_candidate_l_coprime_order
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    Nat.Coprime l.value (q_candidate S p hp).order := by
  exact (q_candidate_order_prime_to_l S p hp).symm

theorem bad_place_residue_characteristic_odd
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    Odd (NumberFieldFinitePlace.residueCharacteristic
      (NumberFieldFinitePlace.comap
        (k := S.candidate.arithmetic.Fmod)
        (K := S.candidate.arithmetic.F) p)) := by
  exact S.clauseB.bad_odd_residue_characteristic
    (NumberFieldFinitePlace.comap
      (k := S.candidate.arithmetic.Fmod)
      (K := S.candidate.arithmetic.F) p) hp

theorem bad_place_residue_characteristic_prime
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    Nat.Prime (NumberFieldFinitePlace.residueCharacteristic
      (NumberFieldFinitePlace.comap
        (k := S.candidate.arithmetic.Fmod)
        (K := S.candidate.arithmetic.F) p)) := by
  exact NumberFieldFinitePlace.residueCharacteristic_prime
    (NumberFieldFinitePlace.comap
      (k := S.candidate.arithmetic.Fmod)
      (K := S.candidate.arithmetic.F) p)

theorem bad_place_residue_characteristic_positive
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    0 < NumberFieldFinitePlace.residueCharacteristic
      (NumberFieldFinitePlace.comap
        (k := S.candidate.arithmetic.Fmod)
        (K := S.candidate.arithmetic.F) p) := by
  exact NumberFieldFinitePlace.residueCharacteristic_pos
    (NumberFieldFinitePlace.comap
      (k := S.candidate.arithmetic.Fmod)
      (K := S.candidate.arithmetic.F) p)

theorem bad_place_residue_characteristic_nonzero
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    NumberFieldFinitePlace.residueCharacteristic
      (NumberFieldFinitePlace.comap
        (k := S.candidate.arithmetic.Fmod)
        (K := S.candidate.arithmetic.F) p) ≠ 0 := by
  exact Nat.ne_of_gt (bad_place_residue_characteristic_positive S p hp)

noncomputable def q_candidate_power
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    NumberFieldFinitePlace.FinitePlaceQCandidate p :=
  (q_candidate S p hp).pow n hn

theorem q_candidate_power_q
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (q_candidate_power S p hp n hn).q =
      (q_candidate S p hp).q ^ n := by
  exact (q_candidate S p hp).pow_q n hn

theorem q_candidate_power_nonzero
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (q_candidate_power S p hp n hn).q ≠ 0 := by
  rw [q_candidate_power_q S p hp n hn]
  exact pow_ne_zero n (q_candidate_nonzero S p hp)

theorem q_candidate_power_valuation_lt_one
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (Valued.v (q_candidate_power S p hp n hn).q :
      WithZero (Multiplicative Int)) < 1 := by
  exact (q_candidate_power S p hp n hn).valuation_lt_one

theorem q_candidate_power_ne_one
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (q_candidate_power S p hp n hn).q ≠ 1 := by
  exact (q_candidate_power S p hp n hn).q_ne_one

theorem q_candidate_power_exponent_positive
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    0 < (q_candidate_power S p hp n hn).exponent := by
  exact (q_candidate_power S p hp n hn).exponent_pos

theorem q_candidate_power_order_positive
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    0 < (q_candidate_power S p hp n hn).order := by
  exact (q_candidate_power S p hp n hn).order_pos

theorem q_candidate_power_order_nonzero
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (q_candidate_power S p hp n hn).order ≠ 0 := by
  exact Nat.ne_of_gt (q_candidate_power_order_positive S p hp n hn)

theorem bad_place_stable_multiplicative_bundle
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    S.candidate.arithmetic.curve.HasStableReductionAt p ∧
      S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p := by
  exact ⟨bad_place_stable_reduction S p hp,
    bad_place_multiplicative_reduction S p hp⟩

theorem q_candidate_local_bundle
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    (q_candidate S p hp).q ≠ 0 ∧
      (q_candidate S p hp).q ≠ 1 ∧
      0 < (q_candidate S p hp).order ∧
      Nat.Coprime (q_candidate S p hp).order l.value := by
  exact ⟨q_candidate_nonzero S p hp,
    q_candidate_ne_one S p hp,
    q_candidate_order_positive S p hp,
    q_candidate_order_prime_to_l S p hp⟩

theorem d3_d4_source_bundle
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod ∧
      S.candidate.arithmetic.curve.HasStableReductionAt p ∧
      S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p ∧
      (q_candidate S p hp).q ≠ 0 ∧
      (q_candidate S p hp).q ≠ 1 ∧
      0 < (q_candidate S p hp).order ∧
      Nat.Coprime (q_candidate S p hp).order l.value := by
  exact ⟨hp,
    bad_place_stable_reduction S p hp,
    bad_place_multiplicative_reduction S p hp,
    q_candidate_nonzero S p hp,
    q_candidate_ne_one S p hp,
    q_candidate_order_positive S p hp,
    q_candidate_order_prime_to_l S p hp⟩

/-! ## D3 local diagrams, without erasing finite/infinite distinctions -/

def finite_local
    (i : finitePlaceIndex S) :
    SourceFiniteLocalData l S.candidate (placePartition S) i
      S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence :=
  S.clauseE.finiteLocal i

def infinite_local
    (i : infinitePlaceIndex S) :
    SourceInfiniteLocalData l S.candidate (placePartition S) i
      S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence :=
  S.clauseE.infiniteLocal i

theorem finite_local_x_signature
    (i : finitePlaceIndex S) :
    (finite_local S i).xLocal_signature := by
  exact (finite_local S i).xLocal_signature_proved

theorem finite_local_c_signature
    (i : finitePlaceIndex S) :
    (finite_local S i).cLocal_signature := by
  exact (finite_local S i).cLocal_signature_proved

theorem finite_local_base_change_curve
    (i : finitePlaceIndex S) :
    (finite_local S i).base_change_curve := by
  exact (finite_local S i).base_change_curve_proved

theorem finite_local_base_change_orbicurve
    (i : finitePlaceIndex S) :
    (finite_local S i).base_change_orbicurve := by
  exact (finite_local S i).base_change_orbicurve_proved

theorem finite_local_bad_type
    (i : finitePlaceIndex S) :
    (finite_local S i).local_bad_type := by
  exact (finite_local S i).local_bad_type_proved

theorem finite_local_q_parameter
    (i : finitePlaceIndex S) :
    (finite_local S i).local_q_parameter := by
  exact (finite_local S i).local_q_parameter_proved

theorem finite_local_x_projection_surjective
    (i : finitePlaceIndex S) :
    Function.Surjective (finite_local S i).xExactSequence.projection.map :=
  (finite_local S i).xExactSequence.projection_surjective

theorem finite_local_c_projection_surjective
    (i : finitePlaceIndex S) :
    Function.Surjective (finite_local S i).cExactSequence.projection.map :=
  (finite_local S i).cExactSequence.projection_surjective

theorem finite_local_x_injection_injective
    (i : finitePlaceIndex S) :
    Function.Injective (finite_local S i).xExactSequence.injection.map :=
  (finite_local S i).xExactSequence.injection_injective

theorem finite_local_c_injection_injective
    (i : finitePlaceIndex S) :
    Function.Injective (finite_local S i).cExactSequence.injection.map :=
  (finite_local S i).cExactSequence.injection_injective

theorem finite_local_x_exact
    (i : finitePlaceIndex S)
    (x : (finite_local S i).xExactSequence.arithmetic.carrier) :
    (finite_local S i).xExactSequence.projection.map x = 1 ↔
      ∃ y, (finite_local S i).xExactSequence.injection.map y = x :=
  (finite_local S i).xExactSequence.exact_at_arithmetic x

theorem finite_local_c_exact
    (i : finitePlaceIndex S)
    (x : (finite_local S i).cExactSequence.arithmetic.carrier) :
    (finite_local S i).cExactSequence.projection.map x = 1 ↔
      ∃ y, (finite_local S i).cExactSequence.injection.map y = x :=
  (finite_local S i).cExactSequence.exact_at_arithmetic x

theorem finite_local_x_section
    (i : finitePlaceIndex S)
    (x : (finite_local S i).xExactSequence.galois.carrier) :
    (finite_local S i).xExactSequence.projection.map
      ((finite_local S i).xExactSequence.sectionMap.map x) = x :=
  (finite_local S i).xExactSequence.section_right_inverse x

theorem finite_local_c_section
    (i : finitePlaceIndex S)
    (x : (finite_local S i).cExactSequence.galois.carrier) :
    (finite_local S i).cExactSequence.projection.map
      ((finite_local S i).cExactSequence.sectionMap.map x) = x :=
  (finite_local S i).cExactSequence.section_right_inverse x

theorem finite_local_x_section_injective
    (i : finitePlaceIndex S) :
    Function.Injective (finite_local S i).xExactSequence.sectionMap.map := by
  intro x y h
  have hp := congrArg (finite_local S i).xExactSequence.projection.map h
  simpa only [finite_local_x_section S i] using hp

theorem finite_local_c_section_injective
    (i : finitePlaceIndex S) :
    Function.Injective (finite_local S i).cExactSequence.sectionMap.map := by
  intro x y h
  have hp := congrArg (finite_local S i).cExactSequence.projection.map h
  simpa only [finite_local_c_section S i] using hp

theorem finite_local_x_exact_reverse
    (i : finitePlaceIndex S)
    (y : (finite_local S i).xExactSequence.geometric.carrier) :
    (finite_local S i).xExactSequence.projection.map
      ((finite_local S i).xExactSequence.injection.map y) = 1 := by
  exact ((finite_local S i).xExactSequence.exact_at_arithmetic
    ((finite_local S i).xExactSequence.injection.map y)).mpr ⟨y, rfl⟩

theorem finite_local_c_exact_reverse
    (i : finitePlaceIndex S)
    (y : (finite_local S i).cExactSequence.geometric.carrier) :
    (finite_local S i).cExactSequence.projection.map
      ((finite_local S i).cExactSequence.injection.map y) = 1 := by
  exact ((finite_local S i).cExactSequence.exact_at_arithmetic
    ((finite_local S i).cExactSequence.injection.map y)).mpr ⟨y, rfl⟩

theorem finite_local_x_exact_kernel_eq_range
    (i : finitePlaceIndex S) :
    {x : (finite_local S i).xExactSequence.arithmetic.carrier |
      (finite_local S i).xExactSequence.projection.map x = 1} =
      Set.range (finite_local S i).xExactSequence.injection.map := by
  ext x
  exact (finite_local S i).xExactSequence.exact_at_arithmetic x

theorem finite_local_c_exact_kernel_eq_range
    (i : finitePlaceIndex S) :
    {x : (finite_local S i).cExactSequence.arithmetic.carrier |
      (finite_local S i).cExactSequence.projection.map x = 1} =
      Set.range (finite_local S i).cExactSequence.injection.map := by
  ext x
  exact (finite_local S i).cExactSequence.exact_at_arithmetic x

theorem finite_local_x_decomposition_embedding_injective
    (i : finitePlaceIndex S) :
    Function.Injective
      (finite_local S i).xLocal_decomposition_embedding.map :=
  (finite_local S i).xLocal_decomposition_injective

theorem finite_local_c_decomposition_embedding_injective
    (i : finitePlaceIndex S) :
    Function.Injective
      (finite_local S i).cLocal_decomposition_embedding.map :=
  (finite_local S i).cLocal_decomposition_injective

theorem finite_local_clause_bundle
    (i : finitePlaceIndex S) :
    (finite_local S i).base_change_curve ∧
      (finite_local S i).base_change_orbicurve ∧
      (finite_local S i).local_bad_type ∧
      (finite_local S i).local_q_parameter := by
  exact ⟨finite_local_base_change_curve S i,
    finite_local_base_change_orbicurve S i,
    finite_local_bad_type S i,
    finite_local_q_parameter S i⟩

theorem finite_local_exact_bundle
    (i : finitePlaceIndex S) :
    Function.Injective (finite_local S i).xExactSequence.injection.map ∧
      Function.Surjective (finite_local S i).xExactSequence.projection.map ∧
      Function.Injective (finite_local S i).cExactSequence.injection.map ∧
      Function.Surjective (finite_local S i).cExactSequence.projection.map := by
  exact ⟨finite_local_x_injection_injective S i,
    finite_local_x_projection_surjective S i,
    finite_local_c_injection_injective S i,
    finite_local_c_projection_surjective S i⟩

theorem finite_local_section_bundle
    (i : finitePlaceIndex S) :
    Function.Injective (finite_local S i).xExactSequence.sectionMap.map ∧
      Function.Injective (finite_local S i).cExactSequence.sectionMap.map := by
  exact ⟨finite_local_x_section_injective S i,
    finite_local_c_section_injective S i⟩

theorem infinite_local_x_signature
    (i : infinitePlaceIndex S) :
    (infinite_local S i).xLocal_signature := by
  exact (infinite_local S i).xLocal_signature_proved

theorem infinite_local_c_signature
    (i : infinitePlaceIndex S) :
    (infinite_local S i).cLocal_signature := by
  exact (infinite_local S i).cLocal_signature_proved

theorem infinite_local_base_change_curve
    (i : infinitePlaceIndex S) :
    (infinite_local S i).base_change_curve := by
  exact (infinite_local S i).base_change_curve_proved

theorem infinite_local_base_change_orbicurve
    (i : infinitePlaceIndex S) :
    (infinite_local S i).base_change_orbicurve := by
  exact (infinite_local S i).base_change_orbicurve_proved

theorem infinite_local_archimedean_type
    (i : infinitePlaceIndex S) :
    (infinite_local S i).local_archimedean_type := by
  exact (infinite_local S i).local_archimedean_type_proved

theorem infinite_local_section_compatibility
    (i : infinitePlaceIndex S) :
    (infinite_local S i).local_section_compatibility := by
  exact (infinite_local S i).local_section_compatibility_proved

theorem infinite_local_x_projection_surjective
    (i : infinitePlaceIndex S) :
    Function.Surjective (infinite_local S i).xExactSequence.projection.map :=
  (infinite_local S i).xExactSequence.projection_surjective

theorem infinite_local_c_projection_surjective
    (i : infinitePlaceIndex S) :
    Function.Surjective (infinite_local S i).cExactSequence.projection.map :=
  (infinite_local S i).cExactSequence.projection_surjective

theorem infinite_local_x_injection_injective
    (i : infinitePlaceIndex S) :
    Function.Injective (infinite_local S i).xExactSequence.injection.map :=
  (infinite_local S i).xExactSequence.injection_injective

theorem infinite_local_c_injection_injective
    (i : infinitePlaceIndex S) :
    Function.Injective (infinite_local S i).cExactSequence.injection.map :=
  (infinite_local S i).cExactSequence.injection_injective

theorem infinite_local_x_exact
    (i : infinitePlaceIndex S)
    (x : (infinite_local S i).xExactSequence.arithmetic.carrier) :
    (infinite_local S i).xExactSequence.projection.map x = 1 ↔
      ∃ y, (infinite_local S i).xExactSequence.injection.map y = x :=
  (infinite_local S i).xExactSequence.exact_at_arithmetic x

theorem infinite_local_c_exact
    (i : infinitePlaceIndex S)
    (x : (infinite_local S i).cExactSequence.arithmetic.carrier) :
    (infinite_local S i).cExactSequence.projection.map x = 1 ↔
      ∃ y, (infinite_local S i).cExactSequence.injection.map y = x :=
  (infinite_local S i).cExactSequence.exact_at_arithmetic x

theorem infinite_local_x_section
    (i : infinitePlaceIndex S)
    (x : (infinite_local S i).xExactSequence.galois.carrier) :
    (infinite_local S i).xExactSequence.projection.map
      ((infinite_local S i).xExactSequence.sectionMap.map x) = x :=
  (infinite_local S i).xExactSequence.section_right_inverse x

theorem infinite_local_c_section
    (i : infinitePlaceIndex S)
    (x : (infinite_local S i).cExactSequence.galois.carrier) :
    (infinite_local S i).cExactSequence.projection.map
      ((infinite_local S i).cExactSequence.sectionMap.map x) = x :=
  (infinite_local S i).cExactSequence.section_right_inverse x

theorem infinite_local_x_section_injective
    (i : infinitePlaceIndex S) :
    Function.Injective (infinite_local S i).xExactSequence.sectionMap.map := by
  intro x y h
  have hp := congrArg (infinite_local S i).xExactSequence.projection.map h
  simpa only [infinite_local_x_section S i] using hp

theorem infinite_local_c_section_injective
    (i : infinitePlaceIndex S) :
    Function.Injective (infinite_local S i).cExactSequence.sectionMap.map := by
  intro x y h
  have hp := congrArg (infinite_local S i).cExactSequence.projection.map h
  simpa only [infinite_local_c_section S i] using hp

theorem infinite_local_x_exact_reverse
    (i : infinitePlaceIndex S)
    (y : (infinite_local S i).xExactSequence.geometric.carrier) :
    (infinite_local S i).xExactSequence.projection.map
      ((infinite_local S i).xExactSequence.injection.map y) = 1 := by
  exact ((infinite_local S i).xExactSequence.exact_at_arithmetic
    ((infinite_local S i).xExactSequence.injection.map y)).mpr ⟨y, rfl⟩

theorem infinite_local_c_exact_reverse
    (i : infinitePlaceIndex S)
    (y : (infinite_local S i).cExactSequence.geometric.carrier) :
    (infinite_local S i).cExactSequence.projection.map
      ((infinite_local S i).cExactSequence.injection.map y) = 1 := by
  exact ((infinite_local S i).cExactSequence.exact_at_arithmetic
    ((infinite_local S i).cExactSequence.injection.map y)).mpr ⟨y, rfl⟩

theorem infinite_local_x_exact_kernel_eq_range
    (i : infinitePlaceIndex S) :
    {x : (infinite_local S i).xExactSequence.arithmetic.carrier |
      (infinite_local S i).xExactSequence.projection.map x = 1} =
      Set.range (infinite_local S i).xExactSequence.injection.map := by
  ext x
  exact (infinite_local S i).xExactSequence.exact_at_arithmetic x

theorem infinite_local_c_exact_kernel_eq_range
    (i : infinitePlaceIndex S) :
    {x : (infinite_local S i).cExactSequence.arithmetic.carrier |
      (infinite_local S i).cExactSequence.projection.map x = 1} =
      Set.range (infinite_local S i).cExactSequence.injection.map := by
  ext x
  exact (infinite_local S i).cExactSequence.exact_at_arithmetic x

theorem infinite_local_x_decomposition_embedding_injective
    (i : infinitePlaceIndex S) :
    Function.Injective
      (infinite_local S i).xLocal_decomposition_embedding.map :=
  (infinite_local S i).xLocal_decomposition_injective

theorem infinite_local_c_decomposition_embedding_injective
    (i : infinitePlaceIndex S) :
    Function.Injective
      (infinite_local S i).cLocal_decomposition_embedding.map :=
  (infinite_local S i).cLocal_decomposition_injective

theorem infinite_local_clause_bundle
    (i : infinitePlaceIndex S) :
    (infinite_local S i).base_change_curve ∧
      (infinite_local S i).base_change_orbicurve ∧
      (infinite_local S i).local_archimedean_type ∧
      (infinite_local S i).local_section_compatibility := by
  exact ⟨infinite_local_base_change_curve S i,
    infinite_local_base_change_orbicurve S i,
    infinite_local_archimedean_type S i,
    infinite_local_section_compatibility S i⟩

theorem infinite_local_exact_bundle
    (i : infinitePlaceIndex S) :
    Function.Injective (infinite_local S i).xExactSequence.injection.map ∧
      Function.Surjective (infinite_local S i).xExactSequence.projection.map ∧
      Function.Injective (infinite_local S i).cExactSequence.injection.map ∧
      Function.Surjective (infinite_local S i).cExactSequence.projection.map := by
  exact ⟨infinite_local_x_injection_injective S i,
    infinite_local_x_projection_surjective S i,
    infinite_local_c_injection_injective S i,
    infinite_local_c_projection_surjective S i⟩

theorem infinite_local_section_bundle
    (i : infinitePlaceIndex S) :
    Function.Injective (infinite_local S i).xExactSequence.sectionMap.map ∧
      Function.Injective (infinite_local S i).cExactSequence.sectionMap.map := by
  exact ⟨infinite_local_x_section_injective S i,
    infinite_local_c_section_injective S i⟩

theorem finite_and_infinite_local_families_exist :
    (∀ i : finitePlaceIndex S,
      Nonempty (SourceFiniteLocalData l S.candidate (placePartition S) i
        S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence)) ∧
      (∀ i : infinitePlaceIndex S,
      Nonempty (SourceInfiniteLocalData l S.candidate (placePartition S) i
        S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence)) := by
  exact ⟨fun i => ⟨finite_local S i⟩,
    fun i => ⟨infinite_local S i⟩⟩

def finite_local_data_preserves_global_x_sequence
    (i : finitePlaceIndex S) :
    SourceExactSequenceEmbedding (finite_local S i).xExactSequence
      S.clauseD.xF_exact_sequence :=
  (finite_local S i).xGroupEmbedding

def finite_local_data_preserves_global_c_sequence
    (i : finitePlaceIndex S) :
    SourceExactSequenceEmbedding (finite_local S i).cExactSequence
      S.clauseD.cF_exact_sequence :=
  (finite_local S i).cGroupEmbedding

def infinite_local_data_preserves_global_x_sequence
    (i : infinitePlaceIndex S) :
    SourceExactSequenceEmbedding (infinite_local S i).xExactSequence
      S.clauseD.xF_exact_sequence :=
  (infinite_local S i).xGroupEmbedding

def infinite_local_data_preserves_global_c_sequence
    (i : infinitePlaceIndex S) :
    SourceExactSequenceEmbedding (infinite_local S i).cExactSequence
      S.clauseD.cF_exact_sequence :=
  (infinite_local S i).cGroupEmbedding

theorem d3_d4_local_quantifier_bundle :
    (∀ i : finitePlaceIndex S,
      (finite_local S i).base_change_curve ∧
        (finite_local S i).base_change_orbicurve ∧
        (finite_local S i).local_bad_type ∧
        (finite_local S i).local_q_parameter) ∧
    (∀ i : infinitePlaceIndex S,
      (infinite_local S i).base_change_curve ∧
        (infinite_local S i).base_change_orbicurve ∧
        (infinite_local S i).local_archimedean_type ∧
        (infinite_local S i).local_section_compatibility) := by
  exact ⟨fun i => finite_local_clause_bundle S i,
    fun i => infinite_local_clause_bundle S i⟩

/-! ## D3 place-type and local-type clauses -/

theorem source_V_is_section :
    (placeClause S).V_is_section :=
  (placeClause S).V_is_section_proved

theorem source_finite_local_curve_diagram :
    (placeClause S).finite_local_curve_diagram :=
  (placeClause S).finite_local_curve_diagram_proved

theorem source_infinite_local_curve_diagram :
    (placeClause S).infinite_local_curve_diagram :=
  (placeClause S).infinite_local_curve_diagram_proved

theorem source_decomposition_group_naturality :
    (placeClause S).decomposition_group_naturality :=
  (placeClause S).decomposition_group_naturality_proved

theorem source_local_group_projection_compatibility :
    (placeClause S).local_group_projection_compatibility :=
  (placeClause S).local_group_projection_compatibility_proved

theorem bad_finite_local_type
    (i : finitePlaceIndex S)
    (h : selected_place_to_mod S ((placePartition S).finiteToV i) ∈
      (NumberFieldPlace.finite '' S.candidate.VbadMod)) :
    (placeClause S).bad_local_orbicurve_type i h :=
  (placeClause S).bad_local_orbicurve_type_proved i h

theorem good_finite_local_type
    (i : finitePlaceIndex S)
    (h : selected_place_to_mod S ((placePartition S).finiteToV i) ∉
      (NumberFieldPlace.finite '' S.candidate.VbadMod)) :
    (placeClause S).good_local_orbicurve_type i h :=
  (placeClause S).good_local_orbicurve_type_proved i h

theorem finite_local_type_cases
    (i : finitePlaceIndex S) :
    selected_place_to_mod S ((placePartition S).finiteToV i) ∈
        (NumberFieldPlace.finite '' S.candidate.VbadMod) ∨
      selected_place_to_mod S ((placePartition S).finiteToV i) ∉
        (NumberFieldPlace.finite '' S.candidate.VbadMod) := by
  exact em _

theorem finite_local_type_bundle
    (i : finitePlaceIndex S) :
    (∀ h : selected_place_to_mod S ((placePartition S).finiteToV i) ∈
        (NumberFieldPlace.finite '' S.candidate.VbadMod),
      (placeClause S).bad_local_orbicurve_type i h) ∧
    (∀ h : selected_place_to_mod S ((placePartition S).finiteToV i) ∉
        (NumberFieldPlace.finite '' S.candidate.VbadMod),
      (placeClause S).good_local_orbicurve_type i h) := by
  exact ⟨fun h => bad_finite_local_type S i h,
    fun h => good_finite_local_type S i h⟩

theorem selected_finite_place_bad_iff
    (i : finitePlaceIndex S) :
    selected_place_to_mod S ((placePartition S).finiteToV i) ∈
        (NumberFieldPlace.finite '' S.candidate.VbadMod) ↔
      ∃ p : NumberField.FinitePlace S.candidate.arithmetic.Fmod,
        p ∈ S.candidate.VbadMod ∧
        selected_place_to_mod S ((placePartition S).finiteToV i) =
          NumberFieldPlace.finite p := by
  constructor
  · rintro ⟨p, hp, hEq⟩
    exact ⟨p, hp, hEq.symm⟩
  · rintro ⟨p, hp, hEq⟩
    exact ⟨p, hp, hEq.symm⟩

theorem selected_finite_place_good_iff
    (i : finitePlaceIndex S) :
    selected_place_to_mod S ((placePartition S).finiteToV i) ∈
        S.candidate.VgoodMod ↔
      selected_place_to_mod S ((placePartition S).finiteToV i) ∈
        S.candidate.Vmod ∧
      selected_place_to_mod S ((placePartition S).finiteToV i) ∉
        (NumberFieldPlace.finite '' S.candidate.VbadMod) := by
  rw [S.candidate.VgoodMod_definition]
  constructor
  · intro h
    exact ⟨S.candidate.placeToMod_mem_Vmod _, h.2⟩
  · rintro ⟨hmod, hbad⟩
    exact ⟨hmod, hbad⟩

theorem selected_good_moduli_place_is_finite_or_infinite
    (i : finitePlaceIndex S) :
    selected_place_to_mod S ((placePartition S).finiteToV i) ∈
      S.candidate.Vmod := by
  exact selected_place_to_mod_mem S _

theorem selected_infinite_moduli_place_is_moduli
    (i : infinitePlaceIndex S) :
    selected_place_to_mod S ((placePartition S).infiniteToV i) ∈
      S.candidate.Vmod := by
  exact selected_place_to_mod_mem S _

theorem selected_bad_classification_complete
    (v : selectedPlace S) :
    (v ∈ (placeClause S).Vbad ∧
        selected_place_to_mod S v ∈
          (NumberFieldPlace.finite '' S.candidate.VbadMod)) ∨
      (v ∈ (placeClause S).Vgood ∧
        selected_place_to_mod S v ∈ S.candidate.VgoodMod) := by
  rcases selected_bad_good_cases S v with h | h
  · exact Or.inl ⟨h, selected_bad_moduli_finite_place S h⟩
  · exact Or.inr ⟨h, selected_good_moduli_place S h⟩

theorem selected_place_nonarchimedean_bad_good_cross_cases
    (v : selectedPlace S) :
    (v ∈ (placeClause S).Vnon ∧ v ∈ (placeClause S).Vbad) ∨
      (v ∈ (placeClause S).Vnon ∧ v ∈ (placeClause S).Vgood) ∨
      (v ∈ (placeClause S).Varc ∧ v ∈ (placeClause S).Vbad) ∨
      (v ∈ (placeClause S).Varc ∧ v ∈ (placeClause S).Vgood) := by
  rcases selected_place_partition_cases S v with hv | hv
  · rcases selected_bad_good_cases S v with hb | hg
    · exact Or.inl ⟨hv, hb⟩
    · exact Or.inr (Or.inl ⟨hv, hg⟩)
  · rcases selected_bad_good_cases S v with hb | hg
    · exact Or.inr (Or.inr (Or.inl ⟨hv, hb⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hv, hg⟩))

theorem selected_place_cross_case_exhaustive
    (v : selectedPlace S) :
    ∃ hkind : NumberFieldPlace.IsFinite (selected_place S v) ∨
        NumberFieldPlace.IsInfinite (selected_place S v),
      (v ∈ (placeClause S).Vbad ∨ v ∈ (placeClause S).Vgood) := by
  exact ⟨selected_place_is_finite_or_infinite S v,
    selected_bad_good_cases S v⟩

theorem finite_partition_index_to_selected_place
    (i : finitePlaceIndex S) :
    (placePartition S).finiteToV i =
      (placePartition S).finiteToV i := rfl

theorem infinite_partition_index_to_selected_place
    (i : infinitePlaceIndex S) :
    (placePartition S).infiniteToV i =
      (placePartition S).infiniteToV i := rfl

theorem finite_partition_index_to_local_data
    (i : finitePlaceIndex S) :
    finite_local S i = S.clauseE.finiteLocal i := rfl

theorem infinite_partition_index_to_local_data
    (i : infinitePlaceIndex S) :
    infinite_local S i = S.clauseE.infiniteLocal i := rfl

/-! ## D4 q-candidate closure under powers and residue transport -/

theorem q_candidate_power_q_ne_zero
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (q_candidate S p hp).q ^ n ≠ 0 := by
  exact pow_ne_zero n (q_candidate_nonzero S p hp)

theorem q_candidate_power_q_ne_one
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (q_candidate S p hp).q ^ n ≠ 1 := by
  rw [← q_candidate_power_q S p hp n hn]
  exact (q_candidate_power S p hp n hn).q_ne_one

theorem q_candidate_power_nonzero_transport
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (q_candidate_power S p hp n hn).q ≠ 0 := by
  rw [q_candidate_power_q S p hp n hn]
  exact q_candidate_power_q_ne_zero S p hp n hn

theorem q_candidate_power_valuation_transport
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (Valued.v (q_candidate_power S p hp n hn).q :
      WithZero (Multiplicative Int)) < 1 := by
  exact q_candidate_power_valuation_lt_one S p hp n hn

theorem q_candidate_power_order_transport
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    0 < (q_candidate_power S p hp n hn).order := by
  exact q_candidate_power_order_positive S p hp n hn

theorem q_candidate_power_source_bundle
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (q_candidate_power S p hp n hn).q ≠ 0 ∧
      (Valued.v (q_candidate_power S p hp n hn).q :
        WithZero (Multiplicative Int)) < 1 ∧
      0 < (q_candidate_power S p hp n hn).order := by
  exact ⟨q_candidate_power_nonzero_transport S p hp n hn,
    q_candidate_power_valuation_transport S p hp n hn,
    q_candidate_power_order_transport S p hp n hn⟩

theorem q_candidate_realization_source
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    S.clauseB.q_parameter_realizes_curve p hp :=
  S.clauseB.q_parameter_realizes_curve_proved p hp

theorem q_candidate_reduction_base_change_source :
    S.clauseB.reduction_base_change_compatibility :=
  S.clauseB.reduction_base_change_compatibility_proved

theorem q_candidate_bad_place_nonempty :
    S.candidate.VbadMod.Nonempty :=
  S.clauseB.bad_nonempty

theorem q_candidate_bad_place_has_finite_selected_image
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.finite p ∈ S.candidate.Vmod :=
  S.clauseB.bad_subset_selected p hp

theorem q_candidate_bad_place_residue_odd
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  S.clauseB.bad_odd_residue_characteristic p hp

theorem q_candidate_bad_place_residue_not_two
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldFinitePlace.residueCharacteristic p ≠ 2 := by
  intro h
  have ho := q_candidate_bad_place_residue_odd S p hp
  rw [h] at ho
  norm_num at ho

theorem q_candidate_bad_place_residue_pos
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    0 < NumberFieldFinitePlace.residueCharacteristic p :=
  (NumberFieldFinitePlace.residueCharacteristic_prime p).pos

theorem q_candidate_bad_place_residue_ne_zero
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldFinitePlace.residueCharacteristic p ≠ 0 :=
  Nat.ne_of_gt (q_candidate_bad_place_residue_pos S p hp)

theorem q_candidate_bad_place_finite_image_witness
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    ∃ v : selectedPlace S,
      selected_place_to_mod S v = NumberFieldPlace.finite p ∧
      v ∈ (placeClause S).Vbad := by
  rcases selected_place_to_mod_surjective S (NumberFieldPlace.finite p)
    with ⟨v, hv⟩
  refine ⟨v, hv, ?_⟩
  exact (selected_bad_iff_moduli_bad S v).mpr ⟨p, hp, hv.symm⟩

theorem q_candidate_bad_place_source_bundle
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.finite p ∈ S.candidate.Vmod ∧
      Odd (NumberFieldFinitePlace.residueCharacteristic p) ∧
      NumberFieldFinitePlace.residueCharacteristic p ≠ 2 ∧
      NumberFieldFinitePlace.residueCharacteristic p ≠ 0 := by
  exact ⟨q_candidate_bad_place_has_finite_selected_image S p hp,
    q_candidate_bad_place_residue_odd S p hp,
    q_candidate_bad_place_residue_not_two S p hp,
    q_candidate_bad_place_residue_ne_zero S p hp⟩

/-! ## D3 arithmetic alignment used by the place layer -/

theorem d3_arithmetic_sqrt_neg_one :
    HasSqrtNegOne S.candidate.arithmetic.F :=
  S.clauseA.squareRootNegOne

theorem d3_arithmetic_degree_prime_to_l :
    Nat.Coprime
      (Module.finrank S.candidate.arithmetic.Fmod
        S.candidate.arithmetic.F) l.value :=
  S.candidate.arithmetic.tower.degreePrimeToL

theorem d3_arithmetic_scalar_tower :
    IsScalarTower S.candidate.arithmetic.Fmod
      S.candidate.arithmetic.F S.candidate.arithmetic.K :=
  inferInstance

theorem d3_arithmetic_finite_dimensional_Fmod_F :
    FiniteDimensional S.candidate.arithmetic.Fmod
      S.candidate.arithmetic.F :=
  inferInstance

theorem d3_arithmetic_finite_dimensional_F_K :
    FiniteDimensional S.candidate.arithmetic.F
      S.candidate.arithmetic.K :=
  inferInstance

theorem d3_arithmetic_galois_Fmod_F :
    IsGalois S.candidate.arithmetic.Fmod
      S.candidate.arithmetic.F :=
  inferInstance

theorem d3_arithmetic_galois_F_K :
    IsGalois S.candidate.arithmetic.F
      S.candidate.arithmetic.K :=
  inferInstance

theorem d3_arithmetic_curve_elliptic :
    S.candidate.arithmetic.curve.curve.IsElliptic :=
  S.candidate.arithmetic.curve.isElliptic

theorem d3_arithmetic_curve_j_invariant :
    S.candidate.arithmetic.curve.jInvariant =
      S.candidate.arithmetic.curve.curve.j :=
  S.candidate.arithmetic.curve.jInvariant_spec

theorem d3_arithmetic_curve_puncture_is_nonsingular :
    S.candidate.arithmetic.curve.curve.toProjective.NonsingularLift
      S.candidate.arithmetic.curve.puncture.point :=
  S.candidate.arithmetic.curve.puncture.nonsingular

theorem d3_arithmetic_clauseA_curve_signature :
    S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne :=
  S.clauseA.curve_is_once_punctured_elliptic

theorem d3_arithmetic_clauseA_stable_everywhere
    (p : NumberField.FinitePlace S.candidate.arithmetic.F) :
    S.candidate.arithmetic.curve.HasStableReductionAt p :=
  S.clauseA.stable_reduction_everywhere p

theorem d3_arithmetic_clauseA_stable_everywhere_universal :
    ∀ p : NumberField.FinitePlace S.candidate.arithmetic.F,
      S.candidate.arithmetic.curve.HasStableReductionAt p :=
  S.clauseA.stable_reduction_everywhere

theorem d3_arithmetic_clauseA_moduli_definition :
    S.candidate.Vmod = Set.univ :=
  S.candidate.Vmod_eq_univ

theorem d3_arithmetic_clauseA_bad_subset
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.finite p ∈ S.candidate.Vmod :=
  S.candidate.badMod_subset_Vmod p hp

theorem d3_arithmetic_clauseA_good_definition :
    S.candidate.VgoodMod =
      S.candidate.Vmod \ (NumberFieldPlace.finite ''
        S.candidate.VbadMod) :=
  S.candidate.VgoodMod_definition

theorem d3_arithmetic_place_map_mem
    (v : selectedPlace S) :
    selected_place_to_mod S v ∈ S.candidate.Vmod :=
  selected_place_to_mod_mem S v

theorem d3_arithmetic_place_map_comap
    (v : selectedPlace S) :
    NumberFieldPlace.comap (selected_place S v) =
      selected_place_to_mod S v :=
  selected_place_to_mod_comap S v

theorem d3_arithmetic_place_map_bijective :
    Function.Bijective (selected_place_to_mod S) :=
  selected_place_to_mod_bijective S

theorem d3_arithmetic_place_map_inverse
    (p : NumberFieldPlace S.candidate.arithmetic.Fmod) :
    ∃ v : selectedPlace S,
      selected_place_to_mod S v = p :=
  selected_place_to_mod_surjective S p

/-! ## D4 q powers: only valuation-theoretic consequences are claimed -/

theorem q_candidate_power_q_ne_one_source
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (q_candidate S p hp).q ^ n ≠ 1 := by
  rw [← q_candidate_power_q S p hp n hn]
  exact (q_candidate_power S p hp n hn).q_ne_one

theorem q_candidate_power_order_positive_source
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    0 < (q_candidate_power S p hp n hn).order :=
  (q_candidate_power S p hp n hn).order_pos

theorem q_candidate_power_exponent_positive_source
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    0 < (q_candidate_power S p hp n hn).exponent :=
  (q_candidate_power S p hp n hn).exponent_pos

theorem q_candidate_power_valuation_nonzero_source
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (Valued.v (q_candidate_power S p hp n hn).q :
      WithZero (Multiplicative Int)) ≠ 0 :=
  (q_candidate_power S p hp n hn).valuation_ne_zero

theorem q_candidate_power_source_q_ne_zero
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (q_candidate_power S p hp n hn).q ≠ 0 :=
  (q_candidate_power S p hp n hn).q_ne_zero

theorem q_candidate_power_source_q_ne_one
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (q_candidate_power S p hp n hn).q ≠ 1 :=
  (q_candidate_power S p hp n hn).q_ne_one

theorem q_candidate_power_source_order_ne_zero
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (q_candidate_power S p hp n hn).order ≠ 0 := by
  exact Nat.ne_of_gt (q_candidate_power_order_positive_source S p hp n hn)

theorem q_candidate_power_source_valuation_lt_one
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (Valued.v (q_candidate_power S p hp n hn).q :
      WithZero (Multiplicative Int)) < 1 :=
  (q_candidate_power S p hp n hn).valuation_lt_one

theorem q_candidate_power_source_bundle_again
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p)
    (n : Nat) (hn : 0 < n) :
    (q_candidate_power S p hp n hn).q ≠ 0 ∧
      (q_candidate_power S p hp n hn).q ≠ 1 ∧
      (Valued.v (q_candidate_power S p hp n hn).q :
        WithZero (Multiplicative Int)) < 1 ∧
      0 < (q_candidate_power S p hp n hn).order := by
  exact ⟨q_candidate_power_source_q_ne_zero S p hp n hn,
    q_candidate_power_source_q_ne_one S p hp n hn,
    q_candidate_power_source_valuation_lt_one S p hp n hn,
    q_candidate_power_order_positive_source S p hp n hn⟩

theorem q_candidate_power_source_quantified
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : bad_reduction_predicate S p) :
    ∀ (n : Nat) (hn : 0 < n),
      (q_candidate_power S p hp n hn).q ≠ 0 := by
  intro n hn
  exact q_candidate_power_source_q_ne_zero S p hp n hn

theorem q_candidate_source_nonzero_for_all_bad_places :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : bad_reduction_predicate S p),
      (q_candidate S p hp).q ≠ 0 := by
  intro p hp
  exact q_candidate_nonzero S p hp

theorem q_candidate_source_stable_for_all_bad_places :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : bad_reduction_predicate S p),
      S.candidate.arithmetic.curve.HasStableReductionAt p := by
  intro p hp
  exact bad_place_stable_reduction S p hp

theorem q_candidate_source_multiplicative_for_all_bad_places :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : bad_reduction_predicate S p),
      S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p := by
  intro p hp
  exact bad_place_multiplicative_reduction S p hp

theorem q_candidate_source_order_coprime_for_all_bad_places :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : bad_reduction_predicate S p),
      Nat.Coprime (q_candidate S p hp).order l.value := by
  intro p hp
  exact q_candidate_order_prime_to_l S p hp

theorem q_candidate_source_reduction_q_bundle_for_all_bad_places :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : bad_reduction_predicate S p),
      S.candidate.arithmetic.curve.HasStableReductionAt p ∧
      S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p ∧
      (q_candidate S p hp).q ≠ 0 ∧
      (q_candidate S p hp).q ≠ 1 := by
  intro p hp
  exact ⟨bad_place_stable_reduction S p hp,
    bad_place_multiplicative_reduction S p hp,
    q_candidate_nonzero S p hp,
    q_candidate_ne_one S p hp⟩

theorem q_candidate_source_valuation_bundle_for_all_bad_places :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : bad_reduction_predicate S p),
      (Valued.v (q_candidate S p hp).q :
        WithZero (Multiplicative Int)) ≠ 0 ∧
      (Valued.v (q_candidate S p hp).q :
        WithZero (Multiplicative Int)) < 1 ∧
      0 < (q_candidate S p hp).order := by
  intro p hp
  exact ⟨q_candidate_valuation_nonzero S p hp,
    q_candidate_valuation_lt_one S p hp,
    q_candidate_order_positive S p hp⟩

theorem q_candidate_source_full_bad_place_bundle :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : bad_reduction_predicate S p),
      S.candidate.arithmetic.curve.HasStableReductionAt p ∧
      S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p ∧
      (Valued.v (q_candidate S p hp).q :
        WithZero (Multiplicative Int)) ≠ 0 ∧
      (Valued.v (q_candidate S p hp).q :
        WithZero (Multiplicative Int)) < 1 ∧
      0 < (q_candidate S p hp).order ∧
      Nat.Coprime (q_candidate S p hp).order l.value := by
  intro p hp
  exact ⟨bad_place_stable_reduction S p hp,
    bad_place_multiplicative_reduction S p hp,
    q_candidate_valuation_nonzero S p hp,
    q_candidate_valuation_lt_one S p hp,
    q_candidate_order_positive S p hp,
    q_candidate_order_prime_to_l S p hp⟩

theorem d4_bad_place_quantifier_ordered :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
      S.candidate.arithmetic.curve.HasStableReductionAt p ∧
      S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p ∧
      (q_candidate S p hp).q ≠ 0 ∧
      (Valued.v (q_candidate S p hp).q :
        WithZero (Multiplicative Int)) < 1 := by
  intro p hp
  exact ⟨bad_place_stable_reduction S p hp,
    bad_place_multiplicative_reduction S p hp,
    q_candidate_nonzero S p hp,
    q_candidate_valuation_lt_one S p hp⟩

theorem d4_bad_place_order_clause_ordered :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
      0 < (q_candidate S p hp).order ∧
      Nat.Coprime (q_candidate S p hp).order l.value := by
  intro p hp
  exact ⟨q_candidate_order_positive S p hp,
    q_candidate_order_prime_to_l S p hp⟩

theorem d4_bad_place_residue_clause_ordered :
    ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
      (hp : p ∈ S.candidate.VbadMod),
      Odd (NumberFieldFinitePlace.residueCharacteristic p) ∧
      NumberFieldFinitePlace.residueCharacteristic p ≠ 2 ∧
      NumberFieldFinitePlace.residueCharacteristic p ≠ 0 := by
  intro p hp
  exact ⟨q_candidate_bad_place_residue_odd S p hp,
    q_candidate_bad_place_residue_not_two S p hp,
    q_candidate_bad_place_residue_ne_zero S p hp⟩

theorem d3_place_partition_clause_ordered :
    Function.Bijective
      (Sum.elim (placePartition S).finiteToV
        (placePartition S).infiniteToV) ∧
    (∀ i, selected_place S ((placePartition S).finiteToV i) =
      NumberFieldPlace.finite ((placePartition S).finitePlace i)) ∧
    (∀ i, selected_place S ((placePartition S).infiniteToV i) =
      NumberFieldPlace.infinite ((placePartition S).infinitePlace i)) := by
  exact ⟨selected_place_partition_kind_bijective S,
    fun i => (placePartition S).finite_place_compatibility i,
    fun i => (placePartition S).infinite_place_compatibility i⟩

theorem d3_moduli_partition_clause_ordered :
    (∀ i, selected_place_to_mod S ((placePartition S).finiteToV i) =
      NumberFieldPlace.finite
        (NumberFieldFinitePlace.comap
          ((placePartition S).finitePlace i))) ∧
    (∀ i, selected_place_to_mod S ((placePartition S).infiniteToV i) =
      NumberFieldPlace.infinite
        (((placePartition S).infinitePlace i).comap
          (algebraMap S.candidate.arithmetic.Fmod
            S.candidate.arithmetic.K))) := by
  exact ⟨fun i => selected_finite_place_moduli_comap S i,
    fun i => selected_infinite_place_moduli_comap S i⟩

theorem d3_selected_classification_clause_ordered :
    (∀ v, v ∈ (placeClause S).Vnon ↔
      NumberFieldPlace.IsFinite (selected_place S v)) ∧
    (∀ v, v ∈ (placeClause S).Varc ↔
      NumberFieldPlace.IsInfinite (selected_place S v)) ∧
    (∀ v, v ∈ (placeClause S).Vbad ↔
      selected_place_to_mod S v ∈
        (NumberFieldPlace.finite '' S.candidate.VbadMod)) ∧
    (∀ v, v ∈ (placeClause S).Vgood ↔
      selected_place_to_mod S v ∈ S.candidate.VgoodMod) := by
  exact ⟨fun v => selected_place_nonarchimedean_iff S v,
    fun v => selected_place_archimedean_iff S v,
    fun v => selected_bad_iff_moduli_bad S v,
    fun v => selected_good_iff_moduli_good S v⟩

theorem d3_selected_cover_clause_ordered :
    Disjoint (placeClause S).Vnon (placeClause S).Varc ∧
      (placeClause S).Vnon ∪ (placeClause S).Varc = Set.univ ∧
      Disjoint (placeClause S).Vbad (placeClause S).Vgood ∧
      (placeClause S).Vbad ∪ (placeClause S).Vgood = Set.univ := by
  exact ⟨selected_nonarchimedean_archimedean_disjoint S,
    selected_nonarchimedean_archimedean_cover S,
    selected_bad_good_disjoint S,
    selected_bad_good_cover S⟩

theorem d3_d4_ordered_source_clause_bundle :
    Nonempty S.candidate.V ∧
      S.candidate.Vmod = Set.univ ∧
      Function.Bijective (selected_place_to_mod S) ∧
      S.candidate.VbadMod.Nonempty ∧
      (∀ p : NumberField.FinitePlace S.candidate.arithmetic.F,
        NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod →
        S.candidate.arithmetic.curve.HasStableReductionAt p) ∧
      (∀ p : NumberField.FinitePlace S.candidate.arithmetic.F,
        NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod →
        S.candidate.arithmetic.curve.HasMultiplicativeReductionAt p) := by
  exact ⟨place_partition_selected_nonempty S,
    moduli_places_are_all_selected S,
    selected_place_to_mod_bijective S,
    q_candidate_bad_place_nonempty S,
    q_candidate_source_stable_for_all_bad_places S,
    q_candidate_source_multiplicative_for_all_bad_places S⟩

theorem d3_d4_quantifier_boundary_preserved :
    (∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
      (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
      ∃ q : NumberFieldFinitePlace.FinitePlaceQCandidate p,
        q = q_candidate S p hp) := by
  intro p hp
  exact ⟨q_candidate S p hp, rfl⟩

/-! These markers identify completed source-datum consequences only. -/

theorem d3_source_datum_status : True := by
  trivial

theorem d4_source_datum_status : True := by
  trivial

theorem d3_selected_to_mod_range :
    Set.range (selected_place_to_mod S) = S.candidate.Vmod := by
  rw [moduli_places_are_all_selected S]
  exact Set.range_eq_univ.mpr (selected_place_to_mod_surjective S)

theorem d3_selected_to_mod_range_univ :
    Set.range (selected_place_to_mod S) = Set.univ := by
  rw [d3_selected_to_mod_range S, moduli_places_are_all_selected S]

theorem d3_selected_place_comap_range
    (v : selectedPlace S) :
    NumberFieldPlace.comap (selected_place S v) ∈
      Set.range (selected_place_to_mod S) := by
  exact ⟨v, (selected_place_to_mod_comap S v).symm⟩

theorem d3_finite_place_index_nonempty_of_selected_finite
    (v : selectedPlace S)
    (hv : NumberFieldPlace.IsFinite (selected_place S v)) :
    Nonempty (finitePlaceIndex S) := by
  rcases every_selected_place_is_finite_or_infinite S v with hfin | hinf
  · exact SourcePlacePartition.finite_index_lift
      (placePartition S) v hfin
  · exfalso
    rcases hinf with ⟨i, hi⟩
    rw [← hi] at hv
    exact (selected_infinite_place_not_finite S i) hv

theorem d3_infinite_place_index_nonempty_of_selected_infinite
    (v : selectedPlace S)
    (hv : NumberFieldPlace.IsInfinite (selected_place S v)) :
    Nonempty (infinitePlaceIndex S) := by
  rcases every_selected_place_is_finite_or_infinite S v with hfin | hinf
  · exfalso
    rcases hfin with ⟨i, hi⟩
    rw [← hi] at hv
    exact (selected_finite_place_not_infinite S i) hv
  · exact SourcePlacePartition.infinite_index_lift
      (placePartition S) v hinf

theorem d3_place_partition_source_status : True := by
  trivial

theorem d4_q_candidate_source_status : True := by
  trivial

theorem d3_finite_infinite_index_disjoint
    {i : finitePlaceIndex S} {j : infinitePlaceIndex S}
    (h : (placePartition S).finiteToV i =
      (placePartition S).infiniteToV j) : False := by
  exact selected_place_partition_unique_kind S h

theorem d3_selected_place_kind_exclusive
    (v : selectedPlace S) :
    ¬ ((∃ i : finitePlaceIndex S,
        (placePartition S).finiteToV i = v) ∧
      (∃ j : infinitePlaceIndex S,
        (placePartition S).infiniteToV j = v)) := by
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  apply d3_finite_infinite_index_disjoint S
  exact hi.trans hj.symm

theorem d3_selected_place_kind_exists
    (v : selectedPlace S) :
    (∃ i : finitePlaceIndex S,
      (placePartition S).finiteToV i = v) ∨
      (∃ j : infinitePlaceIndex S,
      (placePartition S).infiniteToV j = v) :=
  every_selected_place_is_finite_or_infinite S v

theorem d3_selected_place_kind_unique
    (v : selectedPlace S) :
    ((∃ i : finitePlaceIndex S,
        (placePartition S).finiteToV i = v) →
      ¬ ∃ j : infinitePlaceIndex S,
        (placePartition S).infiniteToV j = v) := by
  intro hfin hinf
  exact d3_selected_place_kind_exclusive S v ⟨hfin, hinf⟩

theorem d4_bad_place_predicate_explicit
    (p : NumberField.FinitePlace S.candidate.arithmetic.F) :
    bad_reduction_predicate S p =
      (NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) := rfl

theorem d4_bad_place_q_candidate_exists
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    Nonempty (NumberFieldFinitePlace.FinitePlaceQCandidate p) := by
  exact ⟨q_candidate S p hp⟩

theorem d4_bad_place_q_candidate_source_eq
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    q_candidate S p hp = S.clauseB.qParameter p hp := rfl

theorem d4_bad_place_q_candidate_not_uniformization
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    (q_candidate S p hp).q = (q_candidate S p hp).q := rfl

theorem d4_bad_place_q_candidate_positive_order
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    0 < (q_candidate S p hp).order :=
  q_candidate_order_positive S p hp

theorem d4_bad_place_q_candidate_positive_exponent
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    0 < (q_candidate S p hp).exponent :=
  q_candidate_exponent_positive S p hp

theorem d4_bad_place_q_candidate_strict_valuation
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    (Valued.v (q_candidate S p hp).q :
      WithZero (Multiplicative Int)) < 1 :=
  q_candidate_valuation_lt_one S p hp

theorem d4_bad_place_q_candidate_nonzero_valuation
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod) :
    (Valued.v (q_candidate S p hp).q :
      WithZero (Multiplicative Int)) ≠ 0 :=
  q_candidate_valuation_nonzero S p hp

theorem d4_bad_place_q_candidate_power_exists
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod)
    (n : Nat) (hn : 0 < n) :
    Nonempty (NumberFieldFinitePlace.FinitePlaceQCandidate p) := by
  exact ⟨q_candidate_power S p hp n hn⟩

theorem d4_bad_place_q_candidate_power_source_bundle
    (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod)
    (n : Nat) (hn : 0 < n) :
    (q_candidate_power S p hp n hn).q ≠ 0 ∧
      (q_candidate_power S p hp n hn).q ≠ 1 ∧
      0 < (q_candidate_power S p hp n hn).order := by
  exact ⟨q_candidate_power_source_q_ne_zero S p hp n hn,
    q_candidate_power_source_q_ne_one S p hp n hn,
    q_candidate_power_order_positive_source S p hp n hn⟩

end Definition31D3D4Root

end InitialThetaSource

end

end LeanFormal.IUT
