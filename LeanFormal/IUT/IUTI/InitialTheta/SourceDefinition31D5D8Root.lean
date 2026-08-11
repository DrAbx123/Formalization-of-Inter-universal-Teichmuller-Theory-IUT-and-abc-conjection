import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D3D4Root
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

universe u

/-!
  Source-faithful D5-D8 root consequences for Definition 3.1.

  The parameter is the complete source tuple `SourceInitialThetaData l`.
  Every declaration below consumes an explicitly supplied clause and keeps its
  carrier, map direction, and quantifier.  These are recognition lemmas for a
  qualified source tuple; the arithmetic-to-source construction remains a
  separate D10 obligation.
-/

namespace LeanFormal.IUT

noncomputable section

namespace InitialThetaSource

namespace Definition31D5D8Root

variable {l : PrimeGeFive} (S : SourceInitialThetaData.{u} l)

/-! ## D5: torsion, Galois representation, and large image -/

abbrev torsionClause : ClauseC l S.candidate := S.clauseC

abbrev torsionCarrier : Type u :=
  S.candidate.arithmetic.curve.LTorsion l

def torsionBasis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      S.candidate.arithmetic.curve.LTorsion l :=
  (torsionClause S).torsion_module_basis

def galoisRepresentation :
    (AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  (torsionClause S).galois_representation

def standardSL2Image :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) :=
  (torsionClause S).standard_SL2_image

theorem d5_torsion23_rational :
    PuncturedEllipticCurve.Torsion23Rational
      S.candidate.arithmetic.curve :=
  (torsionClause S).torsion23_rational

theorem d5_torsion_basis_spec :
    torsionBasis S = (torsionClause S).torsion_module_basis := rfl

theorem d5_torsion_basis_surjective :
    Function.Surjective (torsionBasis S) := by
  exact (torsionBasis S).surjective

theorem d5_torsion_basis_injective :
    Function.Injective (torsionBasis S) := by
  exact (torsionBasis S).injective

theorem d5_torsion_basis_bijective :
    Function.Bijective (torsionBasis S) := by
  exact (torsionBasis S).bijective

theorem d5_torsion_basis_mem_range
    (x : S.candidate.arithmetic.curve.LTorsion l) :
    x ∈ Set.range (torsionBasis S) := by
  exact ⟨(torsionBasis S).symm x, (torsionBasis S).apply_symm_apply x⟩

theorem d5_torsion_basis_round_trip
    (x : Fin 2 → ZMod l.value) :
    (torsionBasis S).symm ((torsionBasis S) x) = x := by
  exact (torsionBasis S).symm_apply_apply x

theorem d5_torsion_basis_round_trip_reverse
    (x : S.candidate.arithmetic.curve.LTorsion l) :
    (torsionBasis S) ((torsionBasis S).symm x) = x := by
  exact (torsionBasis S).apply_symm_apply x

theorem d5_galois_representation_canonical :
    galoisRepresentation S =
      S.candidate.arithmetic.curve.galoisLTorsionMatrixRepresentation
        l (torsionBasis S) := by
  exact (torsionClause S).galois_representation_eq_canonical

theorem d5_galois_representation_map_one :
    galoisRepresentation S 1 = 1 := by
  exact (galoisRepresentation S).map_one

theorem d5_galois_representation_map_mul
    (x y : AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F) :
    galoisRepresentation S (x * y) =
      galoisRepresentation S x * galoisRepresentation S y := by
  exact (galoisRepresentation S).map_mul x y

theorem d5_galois_representation_map_inv
    (x : AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F) :
    galoisRepresentation S x⁻¹ =
      (galoisRepresentation S x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← (galoisRepresentation S).map_mul, inv_mul_cancel,
    (galoisRepresentation S).map_one]

theorem d5_galois_representation_map_pow
    (x : AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F)
    (n : Nat) :
    galoisRepresentation S (x ^ n) =
      (galoisRepresentation S x) ^ n := by
  induction n with
  | zero => simp only [pow_zero, (galoisRepresentation S).map_one]
  | succ n ih =>
      rw [pow_succ, (galoisRepresentation S).map_mul, ih, pow_succ]

theorem d5_galois_representation_map_zpow
    (x : AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F)
    (n : Int) :
    galoisRepresentation S (x ^ n) =
      (galoisRepresentation S x) ^ n := by
  cases n with
  | ofNat n =>
      change galoisRepresentation S (x ^ n) =
        (galoisRepresentation S x) ^ n
      exact d5_galois_representation_map_pow S x n
  | negSucc n =>
      simp only [zpow_negSucc]
      rw [d5_galois_representation_map_inv,
        d5_galois_representation_map_pow]

theorem d5_standard_sl2_spec :
    (torsionClause S).standard_SL2_image_spec :=
  (torsionClause S).standard_SL2_image_spec_proved

theorem d5_image_contains_sl2 :
    standardSL2Image S ≤ (galoisRepresentation S).range :=
  (torsionClause S).image_contains_SL2

theorem d5_image_contains_sl2_member
    (g : standardSL2Image S) :
    (g : Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) ∈
      (galoisRepresentation S).range := by
  exact d5_image_contains_sl2 S g.property

theorem d5_kernel_iff
    (x : AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F) :
    x ∈ (galoisRepresentation S).ker ↔
      galoisRepresentation S x = 1 := Iff.rfl

theorem d5_kernel_one :
    (1 : AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F) ∈
      (galoisRepresentation S).ker := by
  exact d5_galois_representation_map_one S

theorem d5_kernel_mul
    {x y : AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F}
    (hx : x ∈ (galoisRepresentation S).ker)
    (hy : y ∈ (galoisRepresentation S).ker) :
    x * y ∈ (galoisRepresentation S).ker := by
  change galoisRepresentation S (x * y) = 1
  change galoisRepresentation S x = 1 at hx
  change galoisRepresentation S y = 1 at hy
  rw [d5_galois_representation_map_mul S, hx, hy, mul_one]

theorem d5_kernel_inv
    {x : AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F}
    (hx : x ∈ (galoisRepresentation S).ker) :
    x⁻¹ ∈ (galoisRepresentation S).ker := by
  change galoisRepresentation S x⁻¹ = 1
  change galoisRepresentation S x = 1 at hx
  rw [d5_galois_representation_map_inv S, hx, inv_one]

theorem d5_kernel_pow
    {x : AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F}
    (hx : x ∈ (galoisRepresentation S).ker) :
    ∀ n : Nat, x ^ n ∈ (galoisRepresentation S).ker := by
  intro n
  induction n with
  | zero => exact d5_kernel_one S
  | succ n ih =>
      rw [pow_succ]
      exact d5_kernel_mul S ih hx

theorem d5_kernel_zpow
    {x : AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F}
    (hx : x ∈ (galoisRepresentation S).ker) :
    ∀ n : Int, x ^ n ∈ (galoisRepresentation S).ker := by
  intro n
  cases n with
  | ofNat n =>
      exact d5_kernel_pow S hx n
  | negSucc n =>
      rw [zpow_negSucc]
      exact d5_kernel_inv S (d5_kernel_pow S hx (n + 1))

theorem d5_kernel_closed
    {x y : AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
      AlgebraicClosure S.candidate.arithmetic.F}
    (hx : x ∈ (galoisRepresentation S).ker)
    (hy : y ∈ (galoisRepresentation S).ker) :
    x * y ∈ (galoisRepresentation S).ker :=
  d5_kernel_mul S hx hy

theorem d5_kernel_field_finite_galois :
    (torsionClause S).kernel_field_finite_galois :=
  (torsionClause S).kernel_field_finite_galois_proved

theorem d5_K_kernel_field_compatibility :
    (torsionClause S).K_kernel_field_compatibility :=
  (torsionClause S).K_kernel_field_compatibility_proved

theorem d5_torsion_action_continuous :
    (torsionClause S).torsion_action_continuous :=
  (torsionClause S).torsion_action_continuous_proved

theorem d5_l_prime : Nat.Prime l.value := l.prime

theorem d5_l_odd : Odd l.value := l.odd

theorem d5_l_ge_five : 5 ≤ l.value := l.ge_five

theorem d5_l_ne_zero : l.value ≠ 0 := Nat.ne_of_gt l.prime.pos

theorem d5_torsion_clause_bundle :
    PuncturedEllipticCurve.Torsion23Rational
        S.candidate.arithmetic.curve ∧
      (torsionClause S).standard_SL2_image_spec ∧
      (torsionClause S).K_kernel_field_compatibility ∧
      (torsionClause S).kernel_field_finite_galois ∧
      (torsionClause S).torsion_action_continuous := by
  exact ⟨d5_torsion23_rational S, d5_standard_sl2_spec S,
    d5_K_kernel_field_compatibility S,
    d5_kernel_field_finite_galois S, d5_torsion_action_continuous S⟩

theorem d5_l_prime_data :
    Nat.Prime l.value ∧ Odd l.value ∧ 5 ≤ l.value ∧ l.value ≠ 0 := by
  exact ⟨d5_l_prime, d5_l_odd, d5_l_ge_five, d5_l_ne_zero⟩

/-! ## D6: orbicurves and the four exact sequences -/

abbrev orbicurveClause : ClauseD l S.candidate := S.clauseD

abbrev xFExact : SourceProfiniteExactSequence :=
  (orbicurveClause S).xF_exact_sequence

abbrev cFExact : SourceProfiniteExactSequence :=
  (orbicurveClause S).cF_exact_sequence

abbrev xKExact : SourceProfiniteExactSequence :=
  (orbicurveClause S).xK_exact_sequence

abbrev cKExact : SourceProfiniteExactSequence :=
  (orbicurveClause S).cK_exact_sequence

def xFToCFEmbedding : SourceExactSequenceEmbedding (xFExact S) (cFExact S) :=
  (orbicurveClause S).xF_cF_group_inclusion

def xKToXFEmbedding : SourceExactSequenceEmbedding (xKExact S) (xFExact S) :=
  (orbicurveClause S).xK_xF_group_inclusion

def cKToCFEmbedding : SourceExactSequenceEmbedding (cKExact S) (cFExact S) :=
  (orbicurveClause S).cK_cF_group_inclusion

theorem d6_xF_signature :
    S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne :=
  (orbicurveClause S).xF_type

theorem d6_cF_signature :
    S.candidate.cF.signature = SourceOrbicurveSignature.typeOneOne :=
  (orbicurveClause S).cF_type

theorem d6_xK_signature :
    S.candidate.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l :=
  (orbicurveClause S).xK_type

theorem d6_cK_signature :
    S.candidate.cK.signature =
      SourceOrbicurveSignature.typeOneLTorsionPlusMinus l :=
  (orbicurveClause S).cK_type

theorem d6_sign_involution_squared :
    (orbicurveClause S).signInvolution_squared :=
  (orbicurveClause S).signInvolution_squared_proved

theorem d6_sign_quotient_invariant :
    (orbicurveClause S).signQuotient_invariant :=
  (orbicurveClause S).signQuotient_invariant_proved

theorem d6_cover_finite_etale :
    (orbicurveClause S).xK_cK_cover.finite_etale :=
  (orbicurveClause S).xK_cK_cover_finite_etale

theorem d6_cartesian_square :
    (orbicurveClause S).xK_cK_cartesian_square :=
  (orbicurveClause S).xK_cK_cartesian_square_proved

theorem d6_cK_determines_xK
    (Y : SourceOrbicurveObject S.candidate.arithmetic.K)
    (hY : Y.signature = SourceOrbicurveSignature.typeOneLTorsion l) :
    Nonempty (Y.carrier ≃ S.candidate.xK.carrier) :=
  (orbicurveClause S).cK_determines_xK Y hY

theorem d6_xF_cF_geometric_injective :
    Function.Injective (xFToCFEmbedding S).geometric.map :=
  (xFToCFEmbedding S).geometric_injective

theorem d6_xF_cF_arithmetic_injective :
    Function.Injective (xFToCFEmbedding S).arithmetic.map :=
  (xFToCFEmbedding S).arithmetic_injective

theorem d6_xF_cF_galois_injective :
    Function.Injective (xFToCFEmbedding S).galois.map :=
  (xFToCFEmbedding S).galois_injective

theorem d6_xK_xF_geometric_injective :
    Function.Injective (xKToXFEmbedding S).geometric.map :=
  (xKToXFEmbedding S).geometric_injective

theorem d6_xK_xF_arithmetic_injective :
    Function.Injective (xKToXFEmbedding S).arithmetic.map :=
  (xKToXFEmbedding S).arithmetic_injective

theorem d6_xK_xF_galois_injective :
    Function.Injective (xKToXFEmbedding S).galois.map :=
  (xKToXFEmbedding S).galois_injective

theorem d6_cK_cF_geometric_injective :
    Function.Injective (cKToCFEmbedding S).geometric.map :=
  (cKToCFEmbedding S).geometric_injective

theorem d6_cK_cF_arithmetic_injective :
    Function.Injective (cKToCFEmbedding S).arithmetic.map :=
  (cKToCFEmbedding S).arithmetic_injective

theorem d6_cK_cF_galois_injective :
    Function.Injective (cKToCFEmbedding S).galois.map :=
  (cKToCFEmbedding S).galois_injective

theorem d6_xF_exact_projection_surjective :
    Function.Surjective (xFExact S).projection.map :=
  (xFExact S).projection_surjective

theorem d6_cF_exact_projection_surjective :
    Function.Surjective (cFExact S).projection.map :=
  (cFExact S).projection_surjective

theorem d6_xK_exact_projection_surjective :
    Function.Surjective (xKExact S).projection.map :=
  (xKExact S).projection_surjective

theorem d6_cK_exact_projection_surjective :
    Function.Surjective (cKExact S).projection.map :=
  (cKExact S).projection_surjective

theorem d6_xF_exact_injection_injective :
    Function.Injective (xFExact S).injection.map :=
  (xFExact S).injection_injective

theorem d6_cF_exact_injection_injective :
    Function.Injective (cFExact S).injection.map :=
  (cFExact S).injection_injective

theorem d6_xK_exact_injection_injective :
    Function.Injective (xKExact S).injection.map :=
  (xKExact S).injection_injective

theorem d6_cK_exact_injection_injective :
    Function.Injective (cKExact S).injection.map :=
  (cKExact S).injection_injective

theorem d6_xF_exact_kernel
    (x : (xFExact S).arithmetic.carrier) :
    (xFExact S).projection.map x = 1 ↔
      ∃ y, (xFExact S).injection.map y = x :=
  (xFExact S).exact_at_arithmetic x

theorem d6_cF_exact_kernel
    (x : (cFExact S).arithmetic.carrier) :
    (cFExact S).projection.map x = 1 ↔
      ∃ y, (cFExact S).injection.map y = x :=
  (cFExact S).exact_at_arithmetic x

theorem d6_xK_exact_kernel
    (x : (xKExact S).arithmetic.carrier) :
    (xKExact S).projection.map x = 1 ↔
      ∃ y, (xKExact S).injection.map y = x :=
  (xKExact S).exact_at_arithmetic x

theorem d6_cK_exact_kernel
    (x : (cKExact S).arithmetic.carrier) :
    (cKExact S).projection.map x = 1 ↔
      ∃ y, (cKExact S).injection.map y = x :=
  (cKExact S).exact_at_arithmetic x

theorem d6_xF_exact_section
    (x : (xFExact S).galois.carrier) :
    (xFExact S).projection.map ((xFExact S).sectionMap.map x) = x :=
  (xFExact S).section_right_inverse x

theorem d6_cF_exact_section
    (x : (cFExact S).galois.carrier) :
    (cFExact S).projection.map ((cFExact S).sectionMap.map x) = x :=
  (cFExact S).section_right_inverse x

theorem d6_xK_exact_section
    (x : (xKExact S).galois.carrier) :
    (xKExact S).projection.map ((xKExact S).sectionMap.map x) = x :=
  (xKExact S).section_right_inverse x

theorem d6_cK_exact_section
    (x : (cKExact S).galois.carrier) :
    (cKExact S).projection.map ((cKExact S).sectionMap.map x) = x :=
  (cKExact S).section_right_inverse x

theorem d6_xF_section_injective :
    Function.Injective (xFExact S).sectionMap.map := by
  exact (xFExact S).section_injective

theorem d6_cF_section_injective :
    Function.Injective (cFExact S).sectionMap.map := by
  exact (cFExact S).section_injective

theorem d6_xK_section_injective :
    Function.Injective (xKExact S).sectionMap.map := by
  exact (xKExact S).section_injective

theorem d6_cK_section_injective :
    Function.Injective (cKExact S).sectionMap.map := by
  exact (cKExact S).section_injective

theorem d6_xF_exact_reverse
    (y : (xFExact S).geometric.carrier) :
    (xFExact S).projection.map ((xFExact S).injection.map y) = 1 :=
  (xFExact S).exact_reverse y

theorem d6_cF_exact_reverse
    (y : (cFExact S).geometric.carrier) :
    (cFExact S).projection.map ((cFExact S).injection.map y) = 1 :=
  (cFExact S).exact_reverse y

theorem d6_xK_exact_reverse
    (y : (xKExact S).geometric.carrier) :
    (xKExact S).projection.map ((xKExact S).injection.map y) = 1 :=
  (xKExact S).exact_reverse y

theorem d6_cK_exact_reverse
    (y : (cKExact S).geometric.carrier) :
    (cKExact S).projection.map ((cKExact S).injection.map y) = 1 :=
  (cKExact S).exact_reverse y

theorem d6_xF_inclusion_square
    (x : (xFExact S).geometric.carrier) :
    (xFToCFEmbedding S).arithmetic.map ((xFExact S).injection.map x) =
      (cFExact S).injection.map ((xFToCFEmbedding S).geometric.map x) :=
  (xFToCFEmbedding S).inclusion_square x

theorem d6_xF_projection_square
    (x : (xFExact S).arithmetic.carrier) :
    (xFToCFEmbedding S).galois.map ((xFExact S).projection.map x) =
      (cFExact S).projection.map ((xFToCFEmbedding S).arithmetic.map x) :=
  (xFToCFEmbedding S).projection_square x

theorem d6_xK_inclusion_square
    (x : (xKExact S).geometric.carrier) :
    (xKToXFEmbedding S).arithmetic.map ((xKExact S).injection.map x) =
      (xFExact S).injection.map ((xKToXFEmbedding S).geometric.map x) :=
  (xKToXFEmbedding S).inclusion_square x

theorem d6_xK_projection_square
    (x : (xKExact S).arithmetic.carrier) :
    (xKToXFEmbedding S).galois.map ((xKExact S).projection.map x) =
      (xFExact S).projection.map ((xKToXFEmbedding S).arithmetic.map x) :=
  (xKToXFEmbedding S).projection_square x

theorem d6_cK_inclusion_square
    (x : (cKExact S).geometric.carrier) :
    (cKToCFEmbedding S).arithmetic.map ((cKExact S).injection.map x) =
      (cFExact S).injection.map ((cKToCFEmbedding S).geometric.map x) :=
  (cKToCFEmbedding S).inclusion_square x

theorem d6_cK_projection_square
    (x : (cKExact S).arithmetic.carrier) :
    (cKToCFEmbedding S).galois.map ((cKExact S).projection.map x) =
      (cFExact S).projection.map ((cKToCFEmbedding S).arithmetic.map x) :=
  (cKToCFEmbedding S).projection_square x

theorem d6_clause_bundle :
    (S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne) ∧
      (S.candidate.cF.signature = SourceOrbicurveSignature.typeOneOne) ∧
      (S.candidate.xK.signature = SourceOrbicurveSignature.typeOneLTorsion l) ∧
      (S.candidate.cK.signature =
        SourceOrbicurveSignature.typeOneLTorsionPlusMinus l) ∧
      (orbicurveClause S).signInvolution_squared ∧
      (orbicurveClause S).signQuotient_invariant ∧
      (orbicurveClause S).xK_cK_cover.finite_etale ∧
      (orbicurveClause S).xK_cK_cartesian_square := by
  exact ⟨d6_xF_signature S, d6_cF_signature S, d6_xK_signature S,
    d6_cK_signature S, d6_sign_involution_squared S,
    d6_sign_quotient_invariant S, d6_cover_finite_etale S,
    d6_cartesian_square S⟩

/-! ## D7: selected sections, local groups, and place clauses -/

abbrev placeClause : ClauseE l S.candidate S.clauseD := S.clauseE

def d7_place_partition : SourcePlacePartition l S.candidate :=
  (placeClause S).placePartition

theorem d7_section_property : (placeClause S).V_is_section :=
  (placeClause S).V_is_section_proved

theorem d7_Vnon_definition (v : S.candidate.V) :
    v ∈ (placeClause S).Vnon ↔
      NumberFieldPlace.IsFinite (S.candidate.place v) :=
  (placeClause S).Vnon_definition v

theorem d7_Varc_definition (v : S.candidate.V) :
    v ∈ (placeClause S).Varc ↔
      NumberFieldPlace.IsInfinite (S.candidate.place v) :=
  (placeClause S).Varc_definition v

theorem d7_Vbad_definition (v : S.candidate.V) :
    v ∈ (placeClause S).Vbad ↔
      S.candidate.placeToMod v ∈
        (NumberFieldPlace.finite '' S.candidate.VbadMod) :=
  (placeClause S).Vbad_definition v

theorem d7_Vgood_definition (v : S.candidate.V) :
    v ∈ (placeClause S).Vgood ↔
      S.candidate.placeToMod v ∈ S.candidate.VgoodMod :=
  (placeClause S).Vgood_definition v

theorem d7_Vnon_arc_disjoint :
    Disjoint (placeClause S).Vnon (placeClause S).Varc :=
  (placeClause S).Vnon_arc_disjoint

theorem d7_Vnon_arc_cover :
    (placeClause S).Vnon ∪ (placeClause S).Varc = Set.univ :=
  (placeClause S).Vnon_arc_cover

theorem d7_Vbad_good_disjoint :
    Disjoint (placeClause S).Vbad (placeClause S).Vgood :=
  (placeClause S).Vbad_good_disjoint

theorem d7_Vbad_good_cover :
    (placeClause S).Vbad ∪ (placeClause S).Vgood = Set.univ :=
  (placeClause S).Vbad_good_cover

theorem d7_Vnon_or_Varc (v : S.candidate.V) :
    v ∈ (placeClause S).Vnon ∨ v ∈ (placeClause S).Varc := by
  have h : v ∈ (placeClause S).Vnon ∪ (placeClause S).Varc := by
    rw [d7_Vnon_arc_cover S]
    exact Set.mem_univ v
  exact h

theorem d7_Vbad_or_Vgood (v : S.candidate.V) :
    v ∈ (placeClause S).Vbad ∨ v ∈ (placeClause S).Vgood := by
  have h : v ∈ (placeClause S).Vbad ∪ (placeClause S).Vgood := by
    rw [d7_Vbad_good_cover S]
    exact Set.mem_univ v
  exact h

theorem d7_not_Varc_of_Vnon {v : S.candidate.V}
    (hv : v ∈ (placeClause S).Vnon) :
    v ∉ (placeClause S).Varc := by
  intro h
  exact Set.disjoint_left.mp (d7_Vnon_arc_disjoint S) hv h

theorem d7_not_Vnon_of_Varc {v : S.candidate.V}
    (hv : v ∈ (placeClause S).Varc) :
    v ∉ (placeClause S).Vnon := by
  intro h
  exact Set.disjoint_left.mp (d7_Vnon_arc_disjoint S) h hv

theorem d7_not_Vgood_of_Vbad {v : S.candidate.V}
    (hv : v ∈ (placeClause S).Vbad) :
    v ∉ (placeClause S).Vgood := by
  intro h
  exact Set.disjoint_left.mp (d7_Vbad_good_disjoint S) hv h

theorem d7_not_Vbad_of_Vgood {v : S.candidate.V}
    (hv : v ∈ (placeClause S).Vgood) :
    v ∉ (placeClause S).Vbad := by
  intro h
  exact Set.disjoint_left.mp (d7_Vbad_good_disjoint S) h hv

def d7_finite_local (i : (d7_place_partition S).finiteIndex) :=
  (placeClause S).finiteLocal i

def d7_infinite_local (i : (d7_place_partition S).infiniteIndex) :=
  (placeClause S).infiniteLocal i

theorem d7_finite_local_signature_x
    (i : (d7_place_partition S).finiteIndex) :
    (d7_finite_local S i).xLocal_signature :=
  (d7_finite_local S i).xLocal_signature_proved

theorem d7_finite_local_signature_c
    (i : (d7_place_partition S).finiteIndex) :
    (d7_finite_local S i).cLocal_signature :=
  (d7_finite_local S i).cLocal_signature_proved

theorem d7_finite_local_base_change_curve
    (i : (d7_place_partition S).finiteIndex) :
    (d7_finite_local S i).base_change_curve :=
  (d7_finite_local S i).base_change_curve_proved

theorem d7_finite_local_base_change_orbicurve
    (i : (d7_place_partition S).finiteIndex) :
    (d7_finite_local S i).base_change_orbicurve :=
  (d7_finite_local S i).base_change_orbicurve_proved

theorem d7_finite_local_bad_type
    (i : (d7_place_partition S).finiteIndex) :
    (d7_finite_local S i).local_bad_type :=
  (d7_finite_local S i).local_bad_type_proved

theorem d7_finite_local_q_parameter
    (i : (d7_place_partition S).finiteIndex) :
    (d7_finite_local S i).local_q_parameter :=
  (d7_finite_local S i).local_q_parameter_proved

theorem d7_finite_local_x_projection_surjective
    (i : (d7_place_partition S).finiteIndex) :
    Function.Surjective (d7_finite_local S i).xExactSequence.projection.map :=
  (d7_finite_local S i).xExactSequence.projection_surjective

theorem d7_finite_local_c_projection_surjective
    (i : (d7_place_partition S).finiteIndex) :
    Function.Surjective (d7_finite_local S i).cExactSequence.projection.map :=
  (d7_finite_local S i).cExactSequence.projection_surjective

theorem d7_finite_local_x_injection_injective
    (i : (d7_place_partition S).finiteIndex) :
    Function.Injective (d7_finite_local S i).xExactSequence.injection.map :=
  (d7_finite_local S i).xExactSequence.injection_injective

theorem d7_finite_local_c_injection_injective
    (i : (d7_place_partition S).finiteIndex) :
    Function.Injective (d7_finite_local S i).cExactSequence.injection.map :=
  (d7_finite_local S i).cExactSequence.injection_injective

theorem d7_finite_local_x_exact
    (i : (d7_place_partition S).finiteIndex)
    (x : (d7_finite_local S i).xExactSequence.arithmetic.carrier) :
    (d7_finite_local S i).xExactSequence.projection.map x = 1 ↔
      ∃ y, (d7_finite_local S i).xExactSequence.injection.map y = x :=
  (d7_finite_local S i).xExactSequence.exact_at_arithmetic x

theorem d7_finite_local_c_exact
    (i : (d7_place_partition S).finiteIndex)
    (x : (d7_finite_local S i).cExactSequence.arithmetic.carrier) :
    (d7_finite_local S i).cExactSequence.projection.map x = 1 ↔
      ∃ y, (d7_finite_local S i).cExactSequence.injection.map y = x :=
  (d7_finite_local S i).cExactSequence.exact_at_arithmetic x

theorem d7_finite_local_x_section
    (i : (d7_place_partition S).finiteIndex)
    (x : (d7_finite_local S i).xExactSequence.galois.carrier) :
    (d7_finite_local S i).xExactSequence.projection.map
      ((d7_finite_local S i).xExactSequence.sectionMap.map x) = x :=
  (d7_finite_local S i).xExactSequence.section_right_inverse x

theorem d7_finite_local_c_section
    (i : (d7_place_partition S).finiteIndex)
    (x : (d7_finite_local S i).cExactSequence.galois.carrier) :
    (d7_finite_local S i).cExactSequence.projection.map
      ((d7_finite_local S i).cExactSequence.sectionMap.map x) = x :=
  (d7_finite_local S i).cExactSequence.section_right_inverse x

theorem d7_finite_local_x_section_injective
    (i : (d7_place_partition S).finiteIndex) :
    Function.Injective (d7_finite_local S i).xExactSequence.sectionMap.map := by
  intro x y h
  have hp := congrArg (d7_finite_local S i).xExactSequence.projection.map h
  simpa only [d7_finite_local_x_section S i] using hp

theorem d7_finite_local_c_section_injective
    (i : (d7_place_partition S).finiteIndex) :
    Function.Injective (d7_finite_local S i).cExactSequence.sectionMap.map := by
  intro x y h
  have hp := congrArg (d7_finite_local S i).cExactSequence.projection.map h
  simpa only [d7_finite_local_c_section S i] using hp

theorem d7_finite_local_x_decomposition_injective
    (i : (d7_place_partition S).finiteIndex) :
    Function.Injective (d7_finite_local S i).xLocal_decomposition_embedding.map :=
  (d7_finite_local S i).xLocal_decomposition_injective

theorem d7_finite_local_c_decomposition_injective
    (i : (d7_place_partition S).finiteIndex) :
    Function.Injective (d7_finite_local S i).cLocal_decomposition_embedding.map :=
  (d7_finite_local S i).cLocal_decomposition_injective

theorem d7_finite_local_bundle
    (i : (d7_place_partition S).finiteIndex) :
    (d7_finite_local S i).base_change_curve ∧
      (d7_finite_local S i).base_change_orbicurve ∧
      (d7_finite_local S i).local_bad_type ∧
      (d7_finite_local S i).local_q_parameter := by
  exact ⟨d7_finite_local_base_change_curve S i,
    d7_finite_local_base_change_orbicurve S i,
    d7_finite_local_bad_type S i, d7_finite_local_q_parameter S i⟩

def d7_finite_local_family :
    ∀ i : (d7_place_partition S).finiteIndex,
      SourceFiniteLocalData l S.candidate (d7_place_partition S) i
        S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence :=
  (placeClause S).finiteLocal

theorem d7_finite_local_curve_diagram :
    (placeClause S).finite_local_curve_diagram :=
  (placeClause S).finite_local_curve_diagram_proved

theorem d7_infinite_local_signature_x
    (i : (d7_place_partition S).infiniteIndex) :
    (d7_infinite_local S i).xLocal_signature :=
  (d7_infinite_local S i).xLocal_signature_proved

theorem d7_infinite_local_signature_c
    (i : (d7_place_partition S).infiniteIndex) :
    (d7_infinite_local S i).cLocal_signature :=
  (d7_infinite_local S i).cLocal_signature_proved

theorem d7_infinite_local_base_change_curve
    (i : (d7_place_partition S).infiniteIndex) :
    (d7_infinite_local S i).base_change_curve :=
  (d7_infinite_local S i).base_change_curve_proved

theorem d7_infinite_local_base_change_orbicurve
    (i : (d7_place_partition S).infiniteIndex) :
    (d7_infinite_local S i).base_change_orbicurve :=
  (d7_infinite_local S i).base_change_orbicurve_proved

theorem d7_infinite_local_archimedean_type
    (i : (d7_place_partition S).infiniteIndex) :
    (d7_infinite_local S i).local_archimedean_type :=
  (d7_infinite_local S i).local_archimedean_type_proved

theorem d7_infinite_local_section_compatibility
    (i : (d7_place_partition S).infiniteIndex) :
    (d7_infinite_local S i).local_section_compatibility :=
  (d7_infinite_local S i).local_section_compatibility_proved

theorem d7_infinite_local_x_projection_surjective
    (i : (d7_place_partition S).infiniteIndex) :
    Function.Surjective (d7_infinite_local S i).xExactSequence.projection.map :=
  (d7_infinite_local S i).xExactSequence.projection_surjective

theorem d7_infinite_local_c_projection_surjective
    (i : (d7_place_partition S).infiniteIndex) :
    Function.Surjective (d7_infinite_local S i).cExactSequence.projection.map :=
  (d7_infinite_local S i).cExactSequence.projection_surjective

theorem d7_infinite_local_x_injection_injective
    (i : (d7_place_partition S).infiniteIndex) :
    Function.Injective (d7_infinite_local S i).xExactSequence.injection.map :=
  (d7_infinite_local S i).xExactSequence.injection_injective

theorem d7_infinite_local_c_injection_injective
    (i : (d7_place_partition S).infiniteIndex) :
    Function.Injective (d7_infinite_local S i).cExactSequence.injection.map :=
  (d7_infinite_local S i).cExactSequence.injection_injective

theorem d7_infinite_local_x_exact
    (i : (d7_place_partition S).infiniteIndex)
    (x : (d7_infinite_local S i).xExactSequence.arithmetic.carrier) :
    (d7_infinite_local S i).xExactSequence.projection.map x = 1 ↔
      ∃ y, (d7_infinite_local S i).xExactSequence.injection.map y = x :=
  (d7_infinite_local S i).xExactSequence.exact_at_arithmetic x

theorem d7_infinite_local_c_exact
    (i : (d7_place_partition S).infiniteIndex)
    (x : (d7_infinite_local S i).cExactSequence.arithmetic.carrier) :
    (d7_infinite_local S i).cExactSequence.projection.map x = 1 ↔
      ∃ y, (d7_infinite_local S i).cExactSequence.injection.map y = x :=
  (d7_infinite_local S i).cExactSequence.exact_at_arithmetic x

theorem d7_infinite_local_x_section
    (i : (d7_place_partition S).infiniteIndex)
    (x : (d7_infinite_local S i).xExactSequence.galois.carrier) :
    (d7_infinite_local S i).xExactSequence.projection.map
      ((d7_infinite_local S i).xExactSequence.sectionMap.map x) = x :=
  (d7_infinite_local S i).xExactSequence.section_right_inverse x

theorem d7_infinite_local_c_section
    (i : (d7_place_partition S).infiniteIndex)
    (x : (d7_infinite_local S i).cExactSequence.galois.carrier) :
    (d7_infinite_local S i).cExactSequence.projection.map
      ((d7_infinite_local S i).cExactSequence.sectionMap.map x) = x :=
  (d7_infinite_local S i).cExactSequence.section_right_inverse x

theorem d7_infinite_local_x_section_injective
    (i : (d7_place_partition S).infiniteIndex) :
    Function.Injective (d7_infinite_local S i).xExactSequence.sectionMap.map := by
  intro x y h
  have hp := congrArg (d7_infinite_local S i).xExactSequence.projection.map h
  simpa only [d7_infinite_local_x_section S i] using hp

theorem d7_infinite_local_c_section_injective
    (i : (d7_place_partition S).infiniteIndex) :
    Function.Injective (d7_infinite_local S i).cExactSequence.sectionMap.map := by
  intro x y h
  have hp := congrArg (d7_infinite_local S i).cExactSequence.projection.map h
  simpa only [d7_infinite_local_c_section S i] using hp

theorem d7_infinite_local_x_decomposition_injective
    (i : (d7_place_partition S).infiniteIndex) :
    Function.Injective (d7_infinite_local S i).xLocal_decomposition_embedding.map :=
  (d7_infinite_local S i).xLocal_decomposition_injective

theorem d7_infinite_local_c_decomposition_injective
    (i : (d7_place_partition S).infiniteIndex) :
    Function.Injective (d7_infinite_local S i).cLocal_decomposition_embedding.map :=
  (d7_infinite_local S i).cLocal_decomposition_injective

theorem d7_infinite_local_bundle
    (i : (d7_place_partition S).infiniteIndex) :
    (d7_infinite_local S i).base_change_curve ∧
      (d7_infinite_local S i).base_change_orbicurve ∧
      (d7_infinite_local S i).local_archimedean_type ∧
      (d7_infinite_local S i).local_section_compatibility := by
  exact ⟨d7_infinite_local_base_change_curve S i,
    d7_infinite_local_base_change_orbicurve S i,
    d7_infinite_local_archimedean_type S i,
    d7_infinite_local_section_compatibility S i⟩

def d7_infinite_local_family :
    ∀ i : (d7_place_partition S).infiniteIndex,
      SourceInfiniteLocalData l S.candidate (d7_place_partition S) i
        S.clauseD.xF_exact_sequence S.clauseD.cF_exact_sequence :=
  (placeClause S).infiniteLocal

theorem d7_infinite_local_curve_diagram :
    (placeClause S).infinite_local_curve_diagram :=
  (placeClause S).infinite_local_curve_diagram_proved

theorem d7_decomposition_group_naturality :
    (placeClause S).decomposition_group_naturality :=
  (placeClause S).decomposition_group_naturality_proved

theorem d7_local_group_projection_compatibility :
    (placeClause S).local_group_projection_compatibility :=
  (placeClause S).local_group_projection_compatibility_proved

theorem d7_bad_local_type
    (i : (d7_place_partition S).finiteIndex)
    (h : S.candidate.placeToMod ((d7_place_partition S).finiteToV i) ∈
      (NumberFieldPlace.finite '' S.candidate.VbadMod)) :
    (placeClause S).bad_local_orbicurve_type i h :=
  (placeClause S).bad_local_orbicurve_type_proved i h

theorem d7_good_local_type
    (i : (d7_place_partition S).finiteIndex)
    (h : S.candidate.placeToMod ((d7_place_partition S).finiteToV i) ∉
      (NumberFieldPlace.finite '' S.candidate.VbadMod)) :
    (placeClause S).good_local_orbicurve_type i h :=
  (placeClause S).good_local_orbicurve_type_proved i h

theorem d7_place_clause_bundle :
    (∀ v : S.candidate.V,
      v ∈ (placeClause S).Vnon ↔
        NumberFieldPlace.IsFinite (S.candidate.place v)) ∧
      (∀ v : S.candidate.V,
        v ∈ (placeClause S).Varc ↔
          NumberFieldPlace.IsInfinite (S.candidate.place v)) ∧
      (∀ v : S.candidate.V,
        v ∈ (placeClause S).Vbad ↔
          S.candidate.placeToMod v ∈
            (NumberFieldPlace.finite '' S.candidate.VbadMod)) ∧
      (∀ v : S.candidate.V,
        v ∈ (placeClause S).Vgood ↔
          S.candidate.placeToMod v ∈ S.candidate.VgoodMod) ∧
      (placeClause S).V_is_section := by
  exact ⟨d7_Vnon_definition S, d7_Varc_definition S,
    d7_Vbad_definition S, d7_Vgood_definition S,
    d7_section_property S⟩

/-! ## D8: cusp and derived orbicurves -/

abbrev cuspClause : ClauseF l S.candidate S.clauseD := S.clauseF

def d8_cusp : SourceCuspDatum S.candidate.epsilonCarrier :=
  (cuspClause S).cusp

def d8_derived_orbicurves :
    SourceCuspDerivedOrbicurves l S.candidate S.clauseD :=
  (cuspClause S).derivedOrbicurves

theorem d8_cusp_epsilon_spec :
    (d8_cusp S).epsilon = (cuspClause S).cusp.epsilon := rfl

theorem d8_cusp_nonzero_quotient :
    (d8_cusp S).nonzero_quotient :=
  (d8_cusp S).nonzero_quotient_proved

theorem d8_cusp_canonical_generator :
    (d8_cusp S).canonical_generator :=
  (d8_cusp S).canonical_generator_proved

theorem d8_cusp_sign_ambiguity :
    (d8_cusp S).sign_ambiguity :=
  (d8_cusp S).sign_ambiguity_proved

theorem d8_derived_xArrow_signature :
    (d8_derived_orbicurves S).xArrow.signature =
      SourceOrbicurveSignature.typeOneLTorsion l :=
  (d8_derived_orbicurves S).xArrow_signature

theorem d8_derived_cArrow_signature :
    (d8_derived_orbicurves S).cArrow.signature =
      SourceOrbicurveSignature.typeOneLTorsionPlusMinus l :=
  (d8_derived_orbicurves S).cArrow_signature

theorem d8_derived_cover_finite_etale :
    (d8_derived_orbicurves S).xArrow_to_cArrow.finite_etale :=
  (d8_derived_orbicurves S).xArrow_cArrow_finite_etale

theorem d8_derived_xArrow_open :
    (d8_derived_orbicurves S).xArrow_geometric_open :=
  (d8_derived_orbicurves S).xArrow_geometric_open_proved

theorem d8_derived_cArrow_open :
    (d8_derived_orbicurves S).cArrow_geometric_open :=
  (d8_derived_orbicurves S).cArrow_geometric_open_proved

theorem d8_cusp_determines_orbicurves :
    (d8_derived_orbicurves S).cusp_determines_orbicurves :=
  (d8_derived_orbicurves S).cusp_determines_orbicurves_proved

theorem d8_cusp_lies_on_cK :
    (cuspClause S).cusp_lies_on_cK :=
  (cuspClause S).cusp_lies_on_cK_proved

theorem d8_cusp_from_nonzero_Q :
    (cuspClause S).cusp_from_nonzero_Q :=
  (cuspClause S).cusp_from_nonzero_Q_proved

theorem d8_cusp_sign_independence :
    (cuspClause S).cusp_sign_independence :=
  (cuspClause S).cusp_sign_independence_proved

theorem d8_cusp_diagram_compatibility :
    (cuspClause S).cusp_diagram_compatibility :=
  (cuspClause S).cusp_diagram_compatibility_proved

theorem d8_derived_xArrow_exact
    (x : (d8_derived_orbicurves S).xArrow_exact_sequence.arithmetic.carrier) :
    (d8_derived_orbicurves S).xArrow_exact_sequence.projection.map x = 1 ↔
      ∃ y, (d8_derived_orbicurves S).xArrow_exact_sequence.injection.map y = x :=
  (d8_derived_orbicurves S).xArrow_exact_sequence.exact_at_arithmetic x

theorem d8_derived_cArrow_exact
    (x : (d8_derived_orbicurves S).cArrow_exact_sequence.arithmetic.carrier) :
    (d8_derived_orbicurves S).cArrow_exact_sequence.projection.map x = 1 ↔
      ∃ y, (d8_derived_orbicurves S).cArrow_exact_sequence.injection.map y = x :=
  (d8_derived_orbicurves S).cArrow_exact_sequence.exact_at_arithmetic x

theorem d8_derived_xArrow_projection_surjective :
    Function.Surjective
      (d8_derived_orbicurves S).xArrow_exact_sequence.projection.map :=
  (d8_derived_orbicurves S).xArrow_exact_sequence.projection_surjective

theorem d8_derived_cArrow_projection_surjective :
    Function.Surjective
      (d8_derived_orbicurves S).cArrow_exact_sequence.projection.map :=
  (d8_derived_orbicurves S).cArrow_exact_sequence.projection_surjective

theorem d8_derived_xArrow_injection_injective :
    Function.Injective
      (d8_derived_orbicurves S).xArrow_exact_sequence.injection.map :=
  (d8_derived_orbicurves S).xArrow_exact_sequence.injection_injective

theorem d8_derived_cArrow_injection_injective :
    Function.Injective
      (d8_derived_orbicurves S).cArrow_exact_sequence.injection.map :=
  (d8_derived_orbicurves S).cArrow_exact_sequence.injection_injective

theorem d8_derived_xArrow_section
    (x : (d8_derived_orbicurves S).xArrow_exact_sequence.galois.carrier) :
    (d8_derived_orbicurves S).xArrow_exact_sequence.projection.map
      ((d8_derived_orbicurves S).xArrow_exact_sequence.sectionMap.map x) = x :=
  (d8_derived_orbicurves S).xArrow_exact_sequence.section_right_inverse x

theorem d8_derived_cArrow_section
    (x : (d8_derived_orbicurves S).cArrow_exact_sequence.galois.carrier) :
    (d8_derived_orbicurves S).cArrow_exact_sequence.projection.map
      ((d8_derived_orbicurves S).cArrow_exact_sequence.sectionMap.map x) = x :=
  (d8_derived_orbicurves S).cArrow_exact_sequence.section_right_inverse x

theorem d8_derived_xArrow_section_injective :
    Function.Injective
      (d8_derived_orbicurves S).xArrow_exact_sequence.sectionMap.map := by
  intro x y h
  have hp := congrArg
    (d8_derived_orbicurves S).xArrow_exact_sequence.projection.map h
  simpa only [d8_derived_xArrow_section S] using hp

theorem d8_derived_cArrow_section_injective :
    Function.Injective
      (d8_derived_orbicurves S).cArrow_exact_sequence.sectionMap.map := by
  intro x y h
  have hp := congrArg
    (d8_derived_orbicurves S).cArrow_exact_sequence.projection.map h
  simpa only [d8_derived_cArrow_section S] using hp

theorem d8_clause_bundle :
    (d8_derived_orbicurves S).xArrow.signature =
        SourceOrbicurveSignature.typeOneLTorsion l ∧
      (d8_derived_orbicurves S).cArrow.signature =
        SourceOrbicurveSignature.typeOneLTorsionPlusMinus l ∧
      (d8_derived_orbicurves S).xArrow_to_cArrow.finite_etale ∧
      (d8_derived_orbicurves S).cusp_determines_orbicurves ∧
      (cuspClause S).cusp_lies_on_cK ∧
      (cuspClause S).cusp_from_nonzero_Q ∧
      (cuspClause S).cusp_sign_independence ∧
      (cuspClause S).cusp_diagram_compatibility := by
  exact ⟨d8_derived_xArrow_signature S, d8_derived_cArrow_signature S,
    d8_derived_cover_finite_etale S, d8_cusp_determines_orbicurves S,
    d8_cusp_lies_on_cK S, d8_cusp_from_nonzero_Q S,
    d8_cusp_sign_independence S, d8_cusp_diagram_compatibility S⟩

/-! ## D9-D11: compatibility records and the faithful source conclusion -/

theorem d9_arithmetic_clause_coherence :
    S.arithmetic_clause_coherence :=
  S.arithmetic_clause_coherence_proved

theorem d9_clause_order_coherence :
    S.clause_order_coherence :=
  S.clause_order_coherence_proved

theorem d9_coherence_bundle :
    S.arithmetic_clause_coherence ∧ S.clause_order_coherence := by
  exact ⟨d9_arithmetic_clause_coherence S, d9_clause_order_coherence S⟩

def d10_complete_clause_records :
    SourceInitialThetaData.SourceInitialThetaClauseRecords S :=
  S.all_six_clause_records

theorem d10_complete_clause_records_clauseA :
    (d10_complete_clause_records S).clauseA = S.clauseA := rfl

theorem d10_complete_clause_records_clauseB :
    (d10_complete_clause_records S).clauseB = S.clauseB := rfl

theorem d10_complete_clause_records_clauseC :
    (d10_complete_clause_records S).clauseC = S.clauseC := rfl

theorem d10_complete_clause_records_clauseD :
    (d10_complete_clause_records S).clauseD = S.clauseD := rfl

theorem d10_complete_clause_records_clauseE :
    (d10_complete_clause_records S).clauseE = S.clauseE := rfl

theorem d10_complete_clause_records_clauseF :
    (d10_complete_clause_records S).clauseF = S.clauseF := rfl

def d11_source_conclusion : InitialThetaDataConclusion S :=
  initialThetaData_conclusion S

def d11_source_conclusion_complete :
    SourceInitialThetaData.SourceInitialThetaClauseRecords S :=
  initialThetaData_conclusion_complete S

theorem d11_source_conclusion_coherence :
    S.arithmetic_clause_coherence ∧ S.clause_order_coherence :=
  initialThetaData_conclusion_coherence S

theorem d11_source_conclusion_clause_a :
    S.candidate.xF.signature = SourceOrbicurveSignature.typeOneOne :=
  S.clauseA.curve_is_once_punctured_elliptic

theorem d11_source_conclusion_clause_b :
    S.candidate.Vmod = Set.univ :=
  (initialThetaData_conclusion_clause_b S).1

theorem d11_source_conclusion_clause_c :
    S.clauseC.standard_SL2_image ≤ S.clauseC.galois_representation.range :=
  S.clauseC.image_contains_SL2

theorem d11_source_conclusion_clause_d :
    S.clauseD.xK_cK_cartesian_square :=
  S.clauseD.xK_cK_cartesian_square_proved

def d11_source_conclusion_clause_e :
    SourcePlacePartition l S.candidate :=
  S.clauseE.placePartition

theorem d11_source_conclusion_clause_e_section :
    S.clauseE.V_is_section :=
  S.clauseE.V_is_section_proved

theorem d11_source_conclusion_clause_f :
    S.clauseF.cusp.nonzero_quotient :=
  S.clauseF.cusp.nonzero_quotient_proved

def d11_source_conclusion_clause_f_derived :
    SourceCuspDerivedOrbicurves l S.candidate S.clauseD :=
  initialThetaData_conclusion_clause_f_derived_orbicurves S

def d11_source_conclusion_all_six :
    SourceInitialThetaData.SourceInitialThetaClauseRecords S :=
  (d11_source_conclusion S).source_clause_records

/-! The following gates are propositions, not theorems.  Their explicit form
    records exactly what is still required for an arithmetic-to-source proof. -/

def d10_arithmetic_to_source_gate : Prop :=
  ∀ (A : InitialThetaArithmeticData.{u} l),
    Nonempty { S : SourceInitialThetaData.{u} l //
      S.candidate.arithmetic = A }

def d11_faithful_conclusion_gate : Prop :=
  ∀ (A : InitialThetaArithmeticData.{u} l),
    Nonempty (PSigma fun S : SourceInitialThetaData.{u} l =>
      PSigma fun (_h : S.candidate.arithmetic = A) =>
        InitialThetaDataConclusion S)

theorem d11_source_tuple_recoverable :
    ∃ T : SourceInitialThetaData.{u} l, T = S :=
  ⟨S, rfl⟩

theorem d11_source_tuple_clause_records_recoverable :
    ∃ R : SourceInitialThetaData.SourceInitialThetaClauseRecords S,
      R = d10_complete_clause_records S :=
  ⟨d10_complete_clause_records S, rfl⟩

theorem d11_source_tuple_candidate_recoverable :
    (d10_complete_clause_records S).clauseA = S.clauseA := rfl

theorem d11_source_tuple_arithmetic_recoverable :
    S.candidate.arithmetic = S.candidate.arithmetic := rfl

theorem d11_quantifier_boundary_preserved :
    (∀ p : NumberField.FinitePlace S.candidate.arithmetic.F,
      NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod →
      S.candidate.arithmetic.curve.HasStableReductionAt p) := by
  intro p hp
  exact S.clauseB.stable_over_bad p hp

theorem d11_no_replacement_by_nonempty :
    (d10_complete_clause_records S).clauseC = S.clauseC := rfl

theorem d11_no_replacement_by_choice :
    (d11_source_conclusion S).source_clause_records =
      d10_complete_clause_records S := by
  rfl

/-! ## Reusable exact-sequence normal forms for D6 and D8 -/

theorem exact_projection_map_one (E : SourceProfiniteExactSequence) :
    E.projection.map 1 = 1 :=
  E.projection.map_one

theorem exact_injection_map_one (E : SourceProfiniteExactSequence) :
    E.injection.map 1 = 1 :=
  E.injection.map_one

theorem exact_section_map_one (E : SourceProfiniteExactSequence) :
    E.sectionMap.map 1 = 1 :=
  E.sectionMap.map_one

theorem exact_projection_map_mul (E : SourceProfiniteExactSequence)
    (x y : E.arithmetic.carrier) :
    E.projection.map (x * y) = E.projection.map x * E.projection.map y :=
  E.projection.map_mul x y

theorem exact_projection_map_inv (E : SourceProfiniteExactSequence)
    (x : E.arithmetic.carrier) :
    E.projection.map x⁻¹ = (E.projection.map x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← E.projection.map_mul, inv_mul_cancel, E.projection.map_one]

theorem exact_projection_map_pow (E : SourceProfiniteExactSequence)
    (x : E.arithmetic.carrier) (n : Nat) :
    E.projection.map (x ^ n) = (E.projection.map x) ^ n := by
  induction n with
  | zero => simpa [pow_zero] using E.projection.map_one
  | succ n ih =>
      rw [pow_succ, E.projection.map_mul, ih, pow_succ]

theorem exact_injection_map_mul (E : SourceProfiniteExactSequence)
    (x y : E.geometric.carrier) :
    E.injection.map (x * y) = E.injection.map x * E.injection.map y :=
  E.injection.map_mul x y

theorem exact_injection_map_inv (E : SourceProfiniteExactSequence)
    (x : E.geometric.carrier) :
    E.injection.map x⁻¹ = (E.injection.map x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← E.injection.map_mul, inv_mul_cancel, E.injection.map_one]

theorem exact_injection_map_pow (E : SourceProfiniteExactSequence)
    (x : E.geometric.carrier) (n : Nat) :
    E.injection.map (x ^ n) = (E.injection.map x) ^ n := by
  induction n with
  | zero => simpa [pow_zero] using E.injection.map_one
  | succ n ih =>
      rw [pow_succ, E.injection.map_mul, ih, pow_succ]

theorem exact_section_map_mul (E : SourceProfiniteExactSequence)
    (x y : E.galois.carrier) :
    E.sectionMap.map (x * y) = E.sectionMap.map x * E.sectionMap.map y :=
  E.sectionMap.map_mul x y

theorem exact_section_map_inv (E : SourceProfiniteExactSequence)
    (x : E.galois.carrier) :
    E.sectionMap.map x⁻¹ = (E.sectionMap.map x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← E.sectionMap.map_mul, inv_mul_cancel, E.sectionMap.map_one]

theorem exact_section_map_pow (E : SourceProfiniteExactSequence)
    (x : E.galois.carrier) (n : Nat) :
    E.sectionMap.map (x ^ n) = (E.sectionMap.map x) ^ n := by
  induction n with
  | zero => simpa [pow_zero] using E.sectionMap.map_one
  | succ n ih =>
      rw [pow_succ, E.sectionMap.map_mul, ih, pow_succ]

theorem exact_section_map_injective (E : SourceProfiniteExactSequence) :
    Function.Injective E.sectionMap.map :=
  E.section_injective

theorem exact_projection_map_surjective (E : SourceProfiniteExactSequence) :
    Function.Surjective E.projection.map :=
  E.projection_surjective

theorem exact_injection_map_injective (E : SourceProfiniteExactSequence) :
    Function.Injective E.injection.map :=
  E.injection_injective

theorem exact_kernel_iff (E : SourceProfiniteExactSequence)
    (x : E.arithmetic.carrier) :
    E.projection.map x = 1 ↔ ∃ y, E.injection.map y = x :=
  E.exact_at_arithmetic x

theorem exact_kernel_witness (E : SourceProfiniteExactSequence)
    (x : E.arithmetic.carrier) (hx : E.projection.map x = 1) :
    ∃ y, E.injection.map y = x :=
  (E.exact_at_arithmetic x).mp hx

theorem exact_kernel_reverse (E : SourceProfiniteExactSequence)
    (y : E.geometric.carrier) :
    E.projection.map (E.injection.map y) = 1 := by
  exact (E.exact_at_arithmetic (E.injection.map y)).mpr ⟨y, rfl⟩

theorem exact_kernel_witness_unique (E : SourceProfiniteExactSequence)
    (x : E.arithmetic.carrier) (hx : E.projection.map x = 1)
    {y z : E.geometric.carrier}
    (hy : E.injection.map y = x) (hz : E.injection.map z = x) : y = z := by
  apply E.injection_injective
  exact hy.trans hz.symm

theorem exact_kernel_range (E : SourceProfiniteExactSequence) :
    {x : E.arithmetic.carrier | E.projection.map x = 1} =
      Set.range E.injection.map := by
  ext x
  change E.projection.map x = 1 ↔ ∃ y, E.injection.map y = x
  exact E.exact_at_arithmetic x

theorem exact_section_right_inverse (E : SourceProfiniteExactSequence)
    (x : E.galois.carrier) :
    E.projection.map (E.sectionMap.map x) = x :=
  E.section_right_inverse x

theorem exact_section_left_cancel (E : SourceProfiniteExactSequence)
    {x y : E.galois.carrier}
    (h : E.sectionMap.map x = E.sectionMap.map y) : x = y := by
  have hp := congrArg E.projection.map h
  simpa only [E.section_right_inverse] using hp

theorem exact_projection_kernel_closed_mul
    (E : SourceProfiniteExactSequence)
    {x y : E.arithmetic.carrier}
    (hx : E.projection.map x = 1) (hy : E.projection.map y = 1) :
    E.projection.map (x * y) = 1 := by
  rw [E.projection.map_mul, hx, hy, mul_one]

theorem exact_projection_kernel_closed_inv
    (E : SourceProfiniteExactSequence)
    {x : E.arithmetic.carrier} (hx : E.projection.map x = 1) :
    E.projection.map x⁻¹ = 1 := by
  rw [exact_projection_map_inv E, hx, inv_one]

theorem exact_projection_kernel_closed_pow
    (E : SourceProfiniteExactSequence)
    {x : E.arithmetic.carrier} (hx : E.projection.map x = 1) :
    ∀ n : Nat, E.projection.map (x ^ n) = 1 := by
  intro n
  induction n with
  | zero => simpa [pow_zero] using E.projection.map_one
  | succ n ih =>
      rw [pow_succ, E.projection.map_mul, ih, hx, one_mul]

theorem exact_injection_kernel_trivial
    (E : SourceProfiniteExactSequence)
    (x : E.geometric.carrier)
    (hx : E.injection.map x = 1) : x = 1 := by
  apply E.injection_injective
  simpa only [E.injection.map_one] using hx

theorem exact_decomposition_exists
    (E : SourceProfiniteExactSequence)
    (x : E.arithmetic.carrier) :
    ∃ y : E.geometric.carrier, E.injection.map y =
      x * (E.sectionMap.map (E.projection.map x))⁻¹ := by
  have hkernel : E.projection.map
      (x * (E.sectionMap.map (E.projection.map x))⁻¹) = 1 := by
    rw [E.projection.map_mul, exact_projection_map_inv E,
      E.section_right_inverse]
    exact mul_inv_cancel _
  exact exact_kernel_witness E _ hkernel

theorem exact_decomposition_reconstruct
    (E : SourceProfiniteExactSequence)
    (x : E.arithmetic.carrier) :
    ∃ y : E.geometric.carrier,
      E.injection.map y * E.sectionMap.map (E.projection.map x) = x := by
  rcases exact_decomposition_exists E x with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  rw [hy, mul_assoc, inv_mul_cancel, mul_one]

theorem exact_decomposition_reconstruct_unique
    (E : SourceProfiniteExactSequence)
    {x : E.arithmetic.carrier}
    {y z : E.geometric.carrier}
    (hy : E.injection.map y * E.sectionMap.map (E.projection.map x) = x)
    (hz : E.injection.map z * E.sectionMap.map (E.projection.map x) = x) :
    y = z := by
  apply E.injection_injective
  apply mul_right_cancel
  exact hy.trans hz.symm

theorem d6_all_exact_sequences_bundle :
    Function.Injective (xFExact S).sectionMap.map ∧
      Function.Injective (cFExact S).sectionMap.map ∧
      Function.Injective (xKExact S).sectionMap.map ∧
      Function.Injective (cKExact S).sectionMap.map := by
  exact ⟨d6_xF_section_injective S, d6_cF_section_injective S,
    d6_xK_section_injective S, d6_cK_section_injective S⟩

theorem d6_all_exact_sequences_surjective :
    Function.Surjective (xFExact S).projection.map ∧
      Function.Surjective (cFExact S).projection.map ∧
      Function.Surjective (xKExact S).projection.map ∧
      Function.Surjective (cKExact S).projection.map := by
  exact ⟨d6_xF_exact_projection_surjective S,
    d6_cF_exact_projection_surjective S,
    d6_xK_exact_projection_surjective S,
    d6_cK_exact_projection_surjective S⟩

theorem d6_all_exact_sequences_injective :
    Function.Injective (xFExact S).injection.map ∧
      Function.Injective (cFExact S).injection.map ∧
      Function.Injective (xKExact S).injection.map ∧
      Function.Injective (cKExact S).injection.map := by
  exact ⟨d6_xF_exact_injection_injective S,
    d6_cF_exact_injection_injective S,
    d6_xK_exact_injection_injective S,
    d6_cK_exact_injection_injective S⟩

theorem d8_derived_exact_bundle :
    Function.Injective
        (d8_derived_orbicurves S).xArrow_exact_sequence.injection.map ∧
      Function.Surjective
        (d8_derived_orbicurves S).xArrow_exact_sequence.projection.map ∧
      Function.Injective
        (d8_derived_orbicurves S).cArrow_exact_sequence.injection.map ∧
      Function.Surjective
        (d8_derived_orbicurves S).cArrow_exact_sequence.projection.map := by
  exact ⟨d8_derived_xArrow_injection_injective S,
    d8_derived_xArrow_projection_surjective S,
    d8_derived_cArrow_injection_injective S,
    d8_derived_cArrow_projection_surjective S⟩

theorem d8_derived_section_bundle :
    Function.Injective
        (d8_derived_orbicurves S).xArrow_exact_sequence.sectionMap.map ∧
      Function.Injective
        (d8_derived_orbicurves S).cArrow_exact_sequence.sectionMap.map := by
  exact ⟨d8_derived_xArrow_section_injective S,
    d8_derived_cArrow_section_injective S⟩

theorem d5_d8_ordered_bundle :
    (torsionClause S).standard_SL2_image ≤
        (torsionClause S).galois_representation.range ∧
      (orbicurveClause S).xK_cK_cartesian_square ∧
      (placeClause S).V_is_section ∧
      (cuspClause S).cusp_diagram_compatibility := by
  exact ⟨(torsionClause S).image_contains_SL2,
    d6_cartesian_square S, d7_section_property S,
    d8_cusp_diagram_compatibility S⟩

theorem exact_projection_map_zpow (E : SourceProfiniteExactSequence)
    (x : E.arithmetic.carrier) (n : Int) :
    E.projection.map (x ^ n) = (E.projection.map x) ^ n := by
  cases n with
  | ofNat n =>
      simpa [zpow_ofNat] using exact_projection_map_pow E x n
  | negSucc n =>
      simp only [zpow_negSucc]
      rw [exact_projection_map_inv E, exact_projection_map_pow E]

theorem exact_injection_map_zpow (E : SourceProfiniteExactSequence)
    (x : E.geometric.carrier) (n : Int) :
    E.injection.map (x ^ n) = (E.injection.map x) ^ n := by
  cases n with
  | ofNat n =>
      simpa [zpow_ofNat] using exact_injection_map_pow E x n
  | negSucc n =>
      simp only [zpow_negSucc]
      rw [exact_injection_map_inv E, exact_injection_map_pow E]

theorem exact_section_map_zpow (E : SourceProfiniteExactSequence)
    (x : E.galois.carrier) (n : Int) :
    E.sectionMap.map (x ^ n) = (E.sectionMap.map x) ^ n := by
  cases n with
  | ofNat n =>
      simpa [zpow_ofNat] using exact_section_map_pow E x n
  | negSucc n =>
      simp only [zpow_negSucc]
      rw [exact_section_map_inv E, exact_section_map_pow E]

theorem exact_projection_section_retraction
    (E : SourceProfiniteExactSequence) :
    E.projection.map ∘ E.sectionMap.map = id := by
  funext x
  exact E.section_right_inverse x

theorem exact_section_map_mem_range
    (E : SourceProfiniteExactSequence) (x : E.galois.carrier) :
    E.sectionMap.map x ∈ Set.range E.sectionMap.map :=
  ⟨x, rfl⟩

theorem exact_injection_map_mem_kernel
    (E : SourceProfiniteExactSequence) (x : E.geometric.carrier) :
    E.injection.map x ∈ E.projection.map ⁻¹' ({1} : Set E.galois.carrier) := by
  change E.projection.map (E.injection.map x) = 1
  exact exact_kernel_reverse E x

theorem exact_kernel_preimage_range
    (E : SourceProfiniteExactSequence) :
    E.projection.map ⁻¹' ({1} : Set E.galois.carrier) =
      Set.range E.injection.map := by
  ext x
  change E.projection.map x = 1 ↔ x ∈ Set.range E.injection.map
  exact exact_kernel_iff E x

theorem d7_finite_place_partition_bijective :
    Function.Bijective
      (Sum.elim (d7_place_partition S).finiteToV
        (d7_place_partition S).infiniteToV) :=
  (d7_place_partition S).kindPartition

theorem d7_finite_place_compatibility
    (i : (d7_place_partition S).finiteIndex) :
    S.candidate.place ((d7_place_partition S).finiteToV i) =
      NumberFieldPlace.finite ((d7_place_partition S).finitePlace i) :=
  (d7_place_partition S).finite_place_compatibility i

theorem d7_infinite_place_compatibility
    (i : (d7_place_partition S).infiniteIndex) :
    S.candidate.place ((d7_place_partition S).infiniteToV i) =
      NumberFieldPlace.infinite ((d7_place_partition S).infinitePlace i) :=
  (d7_place_partition S).infinite_place_compatibility i

theorem d7_finite_moduli_compatibility
    (i : (d7_place_partition S).finiteIndex) :
    S.candidate.placeToMod ((d7_place_partition S).finiteToV i) =
      NumberFieldPlace.finite
        (NumberFieldFinitePlace.comap
          (k := S.candidate.arithmetic.Fmod)
          (K := S.candidate.arithmetic.K)
          ((d7_place_partition S).finitePlace i)) :=
  (d7_place_partition S).finite_moduli_compatibility i

theorem d7_infinite_moduli_compatibility
    (i : (d7_place_partition S).infiniteIndex) :
    S.candidate.placeToMod ((d7_place_partition S).infiniteToV i) =
      NumberFieldPlace.infinite
        (((d7_place_partition S).infinitePlace i).comap
          (algebraMap S.candidate.arithmetic.Fmod
            S.candidate.arithmetic.K)) :=
  (d7_place_partition S).infinite_moduli_compatibility i

theorem d7_selected_place_kind_cases (v : S.candidate.V) :
    (∃ i : (d7_place_partition S).finiteIndex,
      (d7_place_partition S).finiteToV i = v) ∨
      (∃ i : (d7_place_partition S).infiniteIndex,
        (d7_place_partition S).infiniteToV i = v) :=
  (d7_place_partition S).every_selected_place_is_finite_or_infinite v

theorem d8_cusp_data_bundle :
    (d8_cusp S).nonzero_quotient ∧
      (d8_cusp S).canonical_generator ∧
      (d8_cusp S).sign_ambiguity ∧
      (cuspClause S).cusp_lies_on_cK ∧
      (cuspClause S).cusp_from_nonzero_Q := by
  exact ⟨d8_cusp_nonzero_quotient S,
    d8_cusp_canonical_generator S,
    d8_cusp_sign_ambiguity S,
    d8_cusp_lies_on_cK S,
    d8_cusp_from_nonzero_Q S⟩

theorem d8_derived_curve_bundle :
    (d8_derived_orbicurves S).xArrow.signature =
        SourceOrbicurveSignature.typeOneLTorsion l ∧
      (d8_derived_orbicurves S).cArrow.signature =
        SourceOrbicurveSignature.typeOneLTorsionPlusMinus l ∧
      (d8_derived_orbicurves S).xArrow_to_cArrow.finite_etale ∧
      (d8_derived_orbicurves S).xArrow_geometric_open ∧
      (d8_derived_orbicurves S).cArrow_geometric_open := by
  exact ⟨d8_derived_xArrow_signature S,
    d8_derived_cArrow_signature S,
    d8_derived_cover_finite_etale S,
    d8_derived_xArrow_open S,
    d8_derived_cArrow_open S⟩

theorem d9_source_coherence_recoverable :
    S.arithmetic_clause_coherence ∧ S.clause_order_coherence :=
  d9_coherence_bundle S

theorem d11_source_conclusion_recoverable :
    ∃ C : InitialThetaDataConclusion S, C = d11_source_conclusion S :=
  ⟨d11_source_conclusion S, rfl⟩

end Definition31D5D8Root

end InitialThetaSource

end

end LeanFormal.IUT
