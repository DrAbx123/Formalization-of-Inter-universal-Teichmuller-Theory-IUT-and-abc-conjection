import LeanFormal.IUT.IUTI.InitialTheta.Definition31D0D11Aligned

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # Sequential closure of Definition 3.1 from a qualified source datum

  This module contains the one legitimate source-to-ledger adapter.  It does
  not manufacture a source datum from arithmetic data: its input is already
  the six-clause object of Definition 3.1.  The purpose is to make the D0--D11
  order executable and auditable, so that a later arithmetic construction can
  be plugged into one place without duplicating the assembly proof.

  Every declaration below has the predecessor as a dependent index.  In
  particular, D4 consumes the D3 object even though both clauses use the same
  source-level record, and D10/D11 are only the canonical assembly steps.
-/

namespace LeanFormal.IUT

noncomputable section

universe u

namespace Theorem311Source
namespace Definition31D0D11FromSource

open LeanFormal.IUT.InitialThetaSource
open Definition31D0D11Aligned

variable {l : PrimeGeFive}

/-! ## D0 and D1 -/

def d0 (S : SourceInitialThetaData.{u} l) : D0Root.{u} l :=
  D0Root.fromArithmetic S.candidate.arithmetic

def d1 (S : SourceInitialThetaData.{u} l) : D1Root.{u} l :=
  D1Root.of (d0 S)

@[simp] theorem d0_arithmetic (S : SourceInitialThetaData.{u} l) :
    (d0 S).arithmetic = S.candidate.arithmetic :=
  rfl

@[simp] theorem d1_foundation (S : SourceInitialThetaData.{u} l) :
    (d1 S).foundation = d0 S :=
  rfl

theorem d1_prime (S : SourceInitialThetaData.{u} l) :
    Nat.Prime l.value :=
  (d1 S).prime

theorem d1_lower_bound (S : SourceInitialThetaData.{u} l) :
    5 ≤ l.value :=
  (d1 S).lower_bound

theorem d1_odd (S : SourceInitialThetaData.{u} l) :
    Odd l.value :=
  (d1 S).odd

theorem d1_positive (S : SourceInitialThetaData.{u} l) :
    0 < l.value :=
  (d1 S).positive

/-! ## D2: the arithmetic-aligned candidate and clause (a) -/

def d2 (S : SourceInitialThetaData.{u} l) :
    D2Root.{u} (d1 S) where
  candidate := S.candidate
  candidate_arithmetic_eq := rfl
  clauseA := S.clauseA

@[simp] theorem d2_candidate (S : SourceInitialThetaData.{u} l) :
    (d2 S).candidate = S.candidate :=
  rfl

@[simp] theorem d2_arithmetic_alignment (S : SourceInitialThetaData.{u} l) :
    (d2 S).candidate.arithmetic = (d1 S).foundation.arithmetic :=
  rfl

theorem d2_clauseA (S : SourceInitialThetaData.{u} l) :
    (d2 S).clauseA = S.clauseA :=
  rfl

theorem d2_square_root (S : SourceInitialThetaData.{u} l) :
    HasSqrtNegOne (d2 S).candidate.arithmetic.F :=
  (d2 S).clauseA.squareRootNegOne

theorem d2_stable_everywhere (S : SourceInitialThetaData.{u} l)
    (p : NumberField.FinitePlace (d2 S).candidate.arithmetic.F) :
    (d2 S).candidate.arithmetic.curve.HasStableReductionAt p :=
  (d2 S).clauseA.stable_reduction_everywhere p

/-! ## D3: the selected/bad place clause -/

def d3 (S : SourceInitialThetaData.{u} l) :
    D3Root.{u} (d2 S) where
  clauseB := S.clauseB

@[simp] theorem d3_candidate (S : SourceInitialThetaData.{u} l) :
    (d3 S).candidate = S.candidate :=
  rfl

theorem d3_predecessor (S : SourceInitialThetaData.{u} l) :
    D3Root.predecessor (d3 S) = d2 S :=
  rfl

theorem d3_clauseB (S : SourceInitialThetaData.{u} l) :
    (d3 S).clauseB = S.clauseB :=
  rfl

theorem d3_bad_nonempty (S : SourceInitialThetaData.{u} l) :
    (d3 S).candidate.VbadMod.Nonempty :=
  (d3 S).clauseB.bad_nonempty

theorem d3_bad_selected (S : SourceInitialThetaData.{u} l)
    (p : NumberField.FinitePlace (d3 S).candidate.arithmetic.Fmod)
    (hp : p ∈ (d3 S).candidate.VbadMod) :
    NumberFieldPlace.finite p ∈ (d3 S).candidate.Vmod :=
  (d3 S).clauseB.bad_subset_selected p hp

/-! ## D4: reduction and q data -/

def d4 (S : SourceInitialThetaData.{u} l) :
    D4Root.{u} (d3 S) where
  reduction_clause := S.clauseB

@[simp] theorem d4_candidate (S : SourceInitialThetaData.{u} l) :
    (d4 S).candidate = S.candidate :=
  rfl

@[simp] theorem d4_predecessor (S : SourceInitialThetaData.{u} l) :
    D4Root.predecessor (d4 S) = d3 S :=
  rfl

theorem d4_reduction_clause (S : SourceInitialThetaData.{u} l) :
    (d4 S).reduction_clause = S.clauseB :=
  rfl

theorem d4_multiplicative (S : SourceInitialThetaData.{u} l)
    (p : NumberField.FinitePlace (d4 S).candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ (d4 S).candidate.VbadMod) :
    (d4 S).candidate.arithmetic.curve.HasMultiplicativeReductionAt p :=
  (d4 S).reduction_clause.multiplicative_over_bad p hp

theorem d4_stable (S : SourceInitialThetaData.{u} l)
    (p : NumberField.FinitePlace (d4 S).candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ (d4 S).candidate.VbadMod) :
    (d4 S).candidate.arithmetic.curve.HasStableReductionAt p :=
  (d4 S).reduction_clause.stable_over_bad p hp

def d4_qParameter (S : SourceInitialThetaData.{u} l)
    (p : NumberField.FinitePlace (d4 S).candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ (d4 S).candidate.VbadMod) :
    NumberFieldFinitePlace.FinitePlaceQCandidate p :=
  (d4 S).reduction_clause.qParameter p hp

theorem d4_qParameter_coprime (S : SourceInitialThetaData.{u} l)
    (p : NumberField.FinitePlace (d4 S).candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ (d4 S).candidate.VbadMod) :
    Nat.Coprime (d4_qParameter S p hp).order l.value :=
  (d4 S).reduction_clause.q_order_prime_to_l p hp

theorem d4_qParameter_nonzero (S : SourceInitialThetaData.{u} l)
    (p : NumberField.FinitePlace (d4 S).candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ (d4 S).candidate.VbadMod) :
    (d4_qParameter S p hp).q ≠ 0 :=
  (d4_qParameter S p hp).q_ne_zero

theorem d4_qParameter_contracting (S : SourceInitialThetaData.{u} l)
    (p : NumberField.FinitePlace (d4 S).candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ (d4 S).candidate.VbadMod) :
    (Valued.v (d4_qParameter S p hp).q : WithZero (Multiplicative Int)) < 1 :=
  (d4_qParameter S p hp).valuation_lt_one

/-! ## D5: torsion and the representation -/

def d5 (S : SourceInitialThetaData.{u} l) :
    D5Root.{u} (d4 S) where
  torsion_clause := S.clauseC

@[simp] theorem d5_candidate (S : SourceInitialThetaData.{u} l) :
    (d5 S).candidate = S.candidate :=
  rfl

@[simp] theorem d5_predecessor (S : SourceInitialThetaData.{u} l) :
    D5Root.predecessor (d5 S) = d4 S :=
  rfl

theorem d5_torsion_clause (S : SourceInitialThetaData.{u} l) :
    (d5 S).torsion_clause = S.clauseC :=
  rfl

theorem d5_torsion23 (S : SourceInitialThetaData.{u} l) :
    PuncturedEllipticCurve.Torsion23Rational
      (d5 S).candidate.arithmetic.curve :=
  (d5 S).torsion_clause.torsion23_rational

def d5_torsion_basis (S : SourceInitialThetaData.{u} l) :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      (d5 S).candidate.arithmetic.curve.LTorsion l :=
  (d5 S).torsion_clause.torsion_module_basis

def d5_representation (S : SourceInitialThetaData.{u} l) :
    (AlgebraicClosure (d5 S).candidate.arithmetic.F ≃ₐ[
      (d5 S).candidate.arithmetic.F] AlgebraicClosure
        (d5 S).candidate.arithmetic.F) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  (d5 S).torsion_clause.galois_representation

theorem d5_representation_canonical (S : SourceInitialThetaData.{u} l) :
    d5_representation S =
      (d5 S).candidate.arithmetic.curve.galoisLTorsionMatrixRepresentation
        l (d5_torsion_basis S) :=
  (d5 S).torsion_clause.galois_representation_eq_canonical

theorem d5_image_contains (S : SourceInitialThetaData.{u} l) :
    (d5 S).torsion_clause.standard_SL2_image ≤
      (d5_representation S).range :=
  (d5 S).torsion_clause.image_contains_SL2

theorem d5_kernel_finite_galois (S : SourceInitialThetaData.{u} l) :
    (d5 S).torsion_clause.kernel_field_finite_galois :=
  (d5 S).torsion_clause.kernel_field_finite_galois_proved

/-! ## D6: orbicurves and exact sequences -/

def d6 (S : SourceInitialThetaData.{u} l) :
    D6Root.{u} (d5 S) where
  orbicurve_clause := S.clauseD

@[simp] theorem d6_candidate (S : SourceInitialThetaData.{u} l) :
    (d6 S).candidate = S.candidate :=
  rfl

@[simp] theorem d6_predecessor (S : SourceInitialThetaData.{u} l) :
    D6Root.predecessor (d6 S) = d5 S :=
  rfl

theorem d6_orbicurve_clause (S : SourceInitialThetaData.{u} l) :
    (d6 S).orbicurve_clause = S.clauseD :=
  rfl

theorem d6_xK_signature (S : SourceInitialThetaData.{u} l) :
    (d6 S).candidate.xK.signature =
      SourceOrbicurveSignature.typeOneLTorsion l :=
  (d6 S).orbicurve_clause.xK_type

theorem d6_cK_signature (S : SourceInitialThetaData.{u} l) :
    (d6 S).candidate.cK.signature =
      SourceOrbicurveSignature.typeOneLTorsionPlusMinus l :=
  (d6 S).orbicurve_clause.cK_type

theorem d6_xF_exact (S : SourceInitialThetaData.{u} l)
    (x : (d6 S).clause.xF_exact_sequence.arithmetic.carrier) :
    (d6 S).clause.xF_exact_sequence.projection.map x = 1 ↔
      ∃ y, (d6 S).clause.xF_exact_sequence.injection.map y = x :=
  (d6 S).clause.xF_exact_sequence.exact_at_arithmetic x

theorem d6_cF_exact (S : SourceInitialThetaData.{u} l)
    (x : (d6 S).clause.cF_exact_sequence.arithmetic.carrier) :
    (d6 S).clause.cF_exact_sequence.projection.map x = 1 ↔
      ∃ y, (d6 S).clause.cF_exact_sequence.injection.map y = x :=
  (d6 S).clause.cF_exact_sequence.exact_at_arithmetic x

theorem d6_xK_exact (S : SourceInitialThetaData.{u} l)
    (x : (d6 S).clause.xK_exact_sequence.arithmetic.carrier) :
    (d6 S).clause.xK_exact_sequence.projection.map x = 1 ↔
      ∃ y, (d6 S).clause.xK_exact_sequence.injection.map y = x :=
  (d6 S).clause.xK_exact_sequence.exact_at_arithmetic x

theorem d6_cK_exact (S : SourceInitialThetaData.{u} l)
    (x : (d6 S).clause.cK_exact_sequence.arithmetic.carrier) :
    (d6 S).clause.cK_exact_sequence.projection.map x = 1 ↔
      ∃ y, (d6 S).clause.cK_exact_sequence.injection.map y = x :=
  (d6 S).clause.cK_exact_sequence.exact_at_arithmetic x

theorem d6_xF_cF_square (S : SourceInitialThetaData.{u} l)
    (x : (d6 S).clause.xF_exact_sequence.geometric.carrier) :
    (d6 S).clause.xF_cF_group_inclusion.arithmetic.map
        ((d6 S).clause.xF_exact_sequence.injection.map x) =
      (d6 S).clause.cF_exact_sequence.injection.map
        ((d6 S).clause.xF_cF_group_inclusion.geometric.map x) :=
  (d6 S).clause.xF_cF_group_inclusion.inclusion_square x

theorem d6_xK_xF_square (S : SourceInitialThetaData.{u} l)
    (x : (d6 S).clause.xK_exact_sequence.geometric.carrier) :
    (d6 S).clause.xK_xF_group_inclusion.arithmetic.map
        ((d6 S).clause.xK_exact_sequence.injection.map x) =
      (d6 S).clause.xF_exact_sequence.injection.map
        ((d6 S).clause.xK_xF_group_inclusion.geometric.map x) :=
  (d6 S).clause.xK_xF_group_inclusion.inclusion_square x

theorem d6_cK_cF_square (S : SourceInitialThetaData.{u} l)
    (x : (d6 S).clause.cK_exact_sequence.geometric.carrier) :
    (d6 S).clause.cK_cF_group_inclusion.arithmetic.map
        ((d6 S).clause.cK_exact_sequence.injection.map x) =
      (d6 S).clause.cF_exact_sequence.injection.map
        ((d6 S).clause.cK_cF_group_inclusion.geometric.map x) :=
  (d6 S).clause.cK_cF_group_inclusion.inclusion_square x

/-! ## D7: selected places and local data -/

def d7 (S : SourceInitialThetaData.{u} l) :
    D7Root.{u} (d6 S) where
  section_clause := S.clauseE

@[simp] theorem d7_candidate (S : SourceInitialThetaData.{u} l) :
    (d7 S).candidate = S.candidate :=
  rfl

@[simp] theorem d7_predecessor (S : SourceInitialThetaData.{u} l) :
    D7Root.predecessor (d7 S) = d6 S :=
  rfl

theorem d7_section_clause (S : SourceInitialThetaData.{u} l) :
    (d7 S).section_clause = S.clauseE :=
  rfl

theorem d7_section_property (S : SourceInitialThetaData.{u} l) :
    (d7 S).clause.V_is_section :=
  (d7 S).clause.V_is_section_proved

theorem d7_non_arc_partition (S : SourceInitialThetaData.{u} l) :
    Disjoint (d7 S).clause.Vnon (d7 S).clause.Varc ∧
      (d7 S).clause.Vnon ∪ (d7 S).clause.Varc = Set.univ :=
  ⟨(d7 S).clause.Vnon_arc_disjoint, (d7 S).clause.Vnon_arc_cover⟩

theorem d7_bad_good_partition (S : SourceInitialThetaData.{u} l) :
    Disjoint (d7 S).clause.Vbad (d7 S).clause.Vgood ∧
      (d7 S).clause.Vbad ∪ (d7 S).clause.Vgood = Set.univ :=
  ⟨(d7 S).clause.Vbad_good_disjoint, (d7 S).clause.Vbad_good_cover⟩

theorem d7_Vnon_definition (S : SourceInitialThetaData.{u} l)
    (v : (d7 S).candidate.V) :
    v ∈ (d7 S).clause.Vnon ↔
      NumberFieldPlace.IsFinite ((d7 S).candidate.place v) :=
  (d7 S).clause.Vnon_definition v

theorem d7_Varc_definition (S : SourceInitialThetaData.{u} l)
    (v : (d7 S).candidate.V) :
    v ∈ (d7 S).clause.Varc ↔
      NumberFieldPlace.IsInfinite ((d7 S).candidate.place v) :=
  (d7 S).clause.Varc_definition v

def d7_finite_local (S : SourceInitialThetaData.{u} l)
    (i : (d7 S).clause.placePartition.finiteIndex) :
    SourceFiniteLocalData l (d7 S).candidate
      (d7 S).clause.placePartition i
      (d7 S).orbicurve_clause.xF_exact_sequence
      (d7 S).orbicurve_clause.cF_exact_sequence :=
  (d7 S).clause.finiteLocal i

def d7_infinite_local (S : SourceInitialThetaData.{u} l)
    (i : (d7 S).clause.placePartition.infiniteIndex) :
    SourceInfiniteLocalData l (d7 S).candidate
      (d7 S).clause.placePartition i
      (d7 S).orbicurve_clause.xF_exact_sequence
      (d7 S).orbicurve_clause.cF_exact_sequence :=
  (d7 S).clause.infiniteLocal i

/-! ## D8: cusp and derived orbicurves -/

def d8 (S : SourceInitialThetaData.{u} l) :
    D8Root.{u} (d7 S) where
  cusp_clause := S.clauseF

@[simp] theorem d8_candidate (S : SourceInitialThetaData.{u} l) :
    (d8 S).candidate = S.candidate :=
  rfl

@[simp] theorem d8_predecessor (S : SourceInitialThetaData.{u} l) :
    D8Root.predecessor (d8 S) = d7 S :=
  rfl

theorem d8_cusp_clause (S : SourceInitialThetaData.{u} l) :
    (d8 S).cusp_clause = S.clauseF :=
  rfl

theorem d8_cusp_nonzero (S : SourceInitialThetaData.{u} l) :
    (d8 S).cusp.nonzero_quotient :=
  (d8 S).cusp.nonzero_quotient_proved

theorem d8_cusp_canonical (S : SourceInitialThetaData.{u} l) :
    (d8 S).cusp.canonical_generator :=
  (d8 S).cusp.canonical_generator_proved

theorem d8_derived_x_signature (S : SourceInitialThetaData.{u} l) :
    (d8 S).derived.xArrow.signature =
      SourceOrbicurveSignature.typeOneLTorsion l :=
  (d8 S).derived.xArrow_signature

theorem d8_derived_c_signature (S : SourceInitialThetaData.{u} l) :
    (d8 S).derived.cArrow.signature =
      SourceOrbicurveSignature.typeOneLTorsionPlusMinus l :=
  (d8 S).derived.cArrow_signature

theorem d8_derived_cover (S : SourceInitialThetaData.{u} l) :
    (d8 S).derived.xArrow_to_cArrow.finite_etale :=
  (d8 S).derived.xArrow_cArrow_finite_etale

theorem d8_derived_naturality (S : SourceInitialThetaData.{u} l) :
    (d8 S).derived.xArrow_cArrow_naturality :=
  (d8 S).derived.xArrow_cArrow_naturality_proved

/-! ## D9: the two source-level coherence fields -/

def d9 (S : SourceInitialThetaData.{u} l) :
    D9Root.{u} (d8 S) where
  arithmetic_clause_coherence := S.arithmetic_clause_coherence
  arithmetic_clause_coherence_proved := S.arithmetic_clause_coherence_proved
  clause_order_coherence := S.clause_order_coherence
  clause_order_coherence_proved := S.clause_order_coherence_proved

@[simp] theorem d9_predecessor (S : SourceInitialThetaData.{u} l) :
    D9Root.predecessor (d9 S) = d8 S :=
  rfl

theorem d9_arithmetic_coherence (S : SourceInitialThetaData.{u} l) :
    (d9 S).arithmetic_clause_coherence :=
  (d9 S).arithmetic_clause_coherence_proved

theorem d9_order_coherence (S : SourceInitialThetaData.{u} l) :
    (d9 S).clause_order_coherence :=
  (d9 S).clause_order_coherence_proved

/-! ## D10 and D11 -/

def d10 (S : SourceInitialThetaData.{u} l) :
    D10Root.{u} (d9 S) :=
  D10Root.of (d9 S)

def d11 (S : SourceInitialThetaData.{u} l) :
    D11Root.{u} (d10 S) :=
  D11Root.of (d10 S)

def source (S : SourceInitialThetaData.{u} l) :
    SourceInitialThetaData.{u} l :=
  (d10 S).source

def conclusion (S : SourceInitialThetaData.{u} l) :
    InitialThetaDataConclusion (source S) :=
  (d11 S).conclusion

@[simp] theorem d10_source_candidate (S : SourceInitialThetaData.{u} l) :
    (source S).candidate = S.candidate :=
  rfl

@[simp] theorem d10_source_clauseA (S : SourceInitialThetaData.{u} l) :
    (source S).clauseA = S.clauseA :=
  rfl

@[simp] theorem d10_source_clauseB (S : SourceInitialThetaData.{u} l) :
    (source S).clauseB = S.clauseB :=
  rfl

@[simp] theorem d10_source_clauseC (S : SourceInitialThetaData.{u} l) :
    (source S).clauseC = S.clauseC :=
  rfl

@[simp] theorem d10_source_clauseD (S : SourceInitialThetaData.{u} l) :
    (source S).clauseD = S.clauseD :=
  rfl

@[simp] theorem d10_source_clauseE (S : SourceInitialThetaData.{u} l) :
    (source S).clauseE = S.clauseE :=
  rfl

@[simp] theorem d10_source_clauseF (S : SourceInitialThetaData.{u} l) :
    (source S).clauseF = S.clauseF :=
  rfl

theorem d10_source_arithmetic (S : SourceInitialThetaData.{u} l) :
    (source S).candidate.arithmetic = S.candidate.arithmetic :=
  rfl

theorem d10_source_coherence (S : SourceInitialThetaData.{u} l) :
    (source S).arithmetic_clause_coherence ∧
      (source S).clause_order_coherence :=
  ⟨(source S).arithmetic_clause_coherence_proved,
    (source S).clause_order_coherence_proved⟩

theorem d11_conclusion_clause_records (S : SourceInitialThetaData.{u} l) :
    (conclusion S).source_clause_records =
      (source S).all_six_clause_records :=
  rfl

theorem d11_conclusion_recovers_source (S : SourceInitialThetaData.{u} l) :
    (conclusion S).source_clause_records =
      S.all_six_clause_records := by
  rfl

theorem d11_conclusion_coherence (S : SourceInitialThetaData.{u} l) :
    (source S).arithmetic_clause_coherence ∧
      (source S).clause_order_coherence :=
  ⟨(conclusion S).arithmetic_clause_coherence,
    (conclusion S).clause_order_coherence⟩

/-! ## The complete dependent chain -/

def serial (S : SourceInitialThetaData.{u} l) :
    SerialD0D11.{u} S.candidate.arithmetic where
  d2 := d2 S
  d3 := d3 S
  d4 := d4 S
  d5 := d5 S
  d6 := d6 S
  d7 := d7 S
  d8 := d8 S
  d9 := d9 S
  d10 := d10 S
  d11 := d11 S

@[simp] theorem serial_d2 (S : SourceInitialThetaData.{u} l) :
    (serial S).d2 = d2 S :=
  rfl

@[simp] theorem serial_d3 (S : SourceInitialThetaData.{u} l) :
    (serial S).d3 = d3 S :=
  rfl

@[simp] theorem serial_d4 (S : SourceInitialThetaData.{u} l) :
    (serial S).d4 = d4 S :=
  rfl

@[simp] theorem serial_d5 (S : SourceInitialThetaData.{u} l) :
    (serial S).d5 = d5 S :=
  rfl

@[simp] theorem serial_d6 (S : SourceInitialThetaData.{u} l) :
    (serial S).d6 = d6 S :=
  rfl

@[simp] theorem serial_d7 (S : SourceInitialThetaData.{u} l) :
    (serial S).d7 = d7 S :=
  rfl

@[simp] theorem serial_d8 (S : SourceInitialThetaData.{u} l) :
    (serial S).d8 = d8 S :=
  rfl

@[simp] theorem serial_d9 (S : SourceInitialThetaData.{u} l) :
    (serial S).d9 = d9 S :=
  rfl

@[simp] theorem serial_d10 (S : SourceInitialThetaData.{u} l) :
    (serial S).d10 = d10 S :=
  rfl

@[simp] theorem serial_d11 (S : SourceInitialThetaData.{u} l) :
    (serial S).d11 = d11 S :=
  rfl

theorem serial_source (S : SourceInitialThetaData.{u} l) :
    (serial S).source = source S :=
  rfl

theorem serial_conclusion (S : SourceInitialThetaData.{u} l) :
    (serial S).conclusion = conclusion S :=
  rfl

theorem serial_has_all_predecessors (S : SourceInitialThetaData.{u} l) :
    (serial S).d2 = d2 S ∧
      (serial S).d3 = d3 S ∧
      (serial S).d4 = d4 S ∧
      (serial S).d5 = d5 S ∧
      (serial S).d6 = d6 S ∧
      (serial S).d7 = d7 S ∧
      (serial S).d8 = d8 S ∧
      (serial S).d9 = d9 S ∧
      (serial S).d10 = d10 S ∧
      (serial S).d11 = d11 S := by
  exact ⟨serial_d2 S, serial_d3 S, serial_d4 S, serial_d5 S,
    serial_d6 S, serial_d7 S, serial_d8 S, serial_d9 S,
    serial_d10 S, serial_d11 S⟩

/-!
  This theorem is intentionally source-conditional.  The equality in the
  final field records that the adapter preserves the exact source tuple; it
  is not an arithmetic-to-source existence theorem.
-/
theorem serial_conclusion_is_source_faithful
    (S : SourceInitialThetaData.{u} l) :
    (serial S).conclusion.source_clause_records =
      S.all_six_clause_records := by
  rw [serial_conclusion]
  exact d11_conclusion_recovers_source S

end Definition31D0D11FromSource
end Theorem311Source

end
end LeanFormal.IUT
