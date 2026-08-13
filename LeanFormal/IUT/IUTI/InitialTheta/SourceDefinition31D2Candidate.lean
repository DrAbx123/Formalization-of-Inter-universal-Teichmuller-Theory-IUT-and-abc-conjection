import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D2Root
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # D2 output at the complete source-candidate boundary

  `SourceInitialThetaData` is the first object that carries the literal
  Definition 3.1 clauses.  This file connects its arithmetic candidate to the
  D2 root output without projecting any later clause into the arithmetic
  layer.  The square-root agreement below is proof-irrelevance between two
  proofs of the same clause, not a new arithmetic assumption.
-/

namespace LeanFormal.IUT

noncomputable section

universe u

namespace InitialThetaSource
namespace Definition31D2Candidate

open Definition31D2Root

variable {l : PrimeGeFive}

abbrev arithmetic (S : SourceInitialThetaData.{u} l) :
    InitialThetaArithmeticData.{u} l :=
  S.candidate.arithmetic

abbrev output (S : SourceInitialThetaData.{u} l) :
    Definition31D2Root.Output (arithmetic S) :=
  Definition31D2Root.ofArithmetic (arithmetic S)

theorem arithmetic_recovery (S : SourceInitialThetaData.{u} l) :
    arithmetic S = S.candidate.arithmetic := rfl

theorem tower (S : SourceInitialThetaData.{u} l) :
    (output S).tower = S.candidate.arithmetic.tower := rfl

theorem curve (S : SourceInitialThetaData.{u} l) :
    (output S).curve = S.candidate.arithmetic.curve := rfl

theorem sqrtNegOne (S : SourceInitialThetaData.{u} l) :
    HasSqrtNegOne S.candidate.arithmetic.F :=
  (output S).sqrtNegOne

theorem degreePrimeToL (S : SourceInitialThetaData.{u} l) :
    Nat.Coprime
      (Module.finrank S.candidate.arithmetic.Fmod
        S.candidate.arithmetic.F) l.value :=
  (output S).degreePrimeToL

theorem square_root_clause_agreement
    (S : SourceInitialThetaData.{u} l) :
    (output S).sqrtNegOne = S.clauseA.squareRootNegOne := by
  apply Subsingleton.elim

theorem square_root_clause_agreement_heq
    (S : SourceInitialThetaData.{u} l) :
    HEq (output S).sqrtNegOne S.clauseA.squareRootNegOne := by
  exact heq_of_eq (square_root_clause_agreement S)

theorem curve_clause_agreement
    (S : SourceInitialThetaData.{u} l) :
    (output S).curve = S.candidate.arithmetic.curve :=
  curve S

theorem candidate_tower_pair (S : SourceInitialThetaData.{u} l) :
    HasSqrtNegOne S.candidate.arithmetic.F ∧
      Nat.Coprime
        (Module.finrank S.candidate.arithmetic.Fmod
          S.candidate.arithmetic.F) l.value :=
  ⟨sqrtNegOne S, degreePrimeToL S⟩

theorem candidate_carrier_pair (S : SourceInitialThetaData.{u} l) :
    (output S).tower = S.candidate.arithmetic.tower ∧
      (output S).curve = S.candidate.arithmetic.curve :=
  ⟨tower S, curve S⟩

theorem candidate_root_recovery (S : SourceInitialThetaData.{u} l) :
    (output S).sqrtNegOne = S.clauseA.squareRootNegOne ∧
      (output S).tower = S.candidate.arithmetic.tower ∧
      (output S).curve = S.candidate.arithmetic.curve :=
  ⟨square_root_clause_agreement S, tower S, curve S⟩

theorem candidate_l_prime_data (S : SourceInitialThetaData.{u} l) :
    Odd l.value ∧ 5 ≤ l.value ∧ l.value ≠ 0 := by
  exact ⟨l.odd, l.ge_five, l.prime.ne_zero⟩

theorem candidate_field_data (S : SourceInitialThetaData.{u} l) :
    Nonempty (Field S.candidate.arithmetic.Fmod) ∧
      Nonempty (Field S.candidate.arithmetic.F) ∧
      Nonempty (Field S.candidate.arithmetic.K) := by
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

theorem candidate_number_field_data (S : SourceInitialThetaData.{u} l) :
    NumberField S.candidate.arithmetic.Fmod ∧
      NumberField S.candidate.arithmetic.F ∧
      NumberField S.candidate.arithmetic.K := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem candidate_algebra_data (S : SourceInitialThetaData.{u} l) :
    Nonempty (Algebra S.candidate.arithmetic.Fmod S.candidate.arithmetic.F) ∧
      Nonempty (Algebra S.candidate.arithmetic.F S.candidate.arithmetic.K) ∧
      Nonempty (Algebra S.candidate.arithmetic.Fmod S.candidate.arithmetic.K) := by
  exact ⟨⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩⟩

theorem candidate_finite_galois_data
    (S : SourceInitialThetaData.{u} l) :
    FiniteDimensional S.candidate.arithmetic.Fmod
        S.candidate.arithmetic.F ∧
      FiniteDimensional S.candidate.arithmetic.F
        S.candidate.arithmetic.K ∧
      IsGalois S.candidate.arithmetic.Fmod
        S.candidate.arithmetic.F ∧
      IsGalois S.candidate.arithmetic.F
        S.candidate.arithmetic.K := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

theorem candidate_d2_bundle (S : SourceInitialThetaData.{u} l) :
    (output S).tower = S.candidate.arithmetic.tower ∧
      (output S).curve = S.candidate.arithmetic.curve ∧
      HasSqrtNegOne S.candidate.arithmetic.F ∧
      Nat.Coprime
        (Module.finrank S.candidate.arithmetic.Fmod
          S.candidate.arithmetic.F) l.value := by
  exact ⟨tower S, curve S, sqrtNegOne S, degreePrimeToL S⟩

theorem d2_candidate_status : True := by
  trivial

end Definition31D2Candidate
end InitialThetaSource

end
