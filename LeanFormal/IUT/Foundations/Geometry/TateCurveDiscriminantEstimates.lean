/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Foundations.Geometry.TateCurvePadicEstimates

/-!
# The discriminant of the canonical p-adic Tate equation

This module closes the q-series discriminant obligation left open by the
principal-term packet.  It uses only the already proved estimates for the
canonical coefficients.  The term `-a₆` has norm `‖q‖`; each of the four
remaining terms in the expanded discriminant has strictly smaller norm.
The non-archimedean maximum lemma therefore gives both non-vanishing and the
exact norm of the discriminant.

No Tate uniformization, identification with an input elliptic curve, or
minimal-model assertion is made here.  In particular, this is a q-series
ellipticity result, not yet the local reduction theorem needed by IUT I.
-/

namespace LeanFormal.IUT

noncomputable section

namespace TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

section NamesAndDecompositions

def a4Value : ℚ_[l.value] := TateCurve.a4 ℚ_[l.value] (q l)

def a6Value : ℚ_[l.value] := TateCurve.a6 ℚ_[l.value] (q l)

def deltaValue : ℚ_[l.value] := (canonicalCurve l).Δ

def deltaSquareTerm : ℚ_[l.value] := (a4Value l) ^ 2

def deltaA4CubeTerm : ℚ_[l.value] :=
  -(64 : ℚ_[l.value]) * (a4Value l) ^ 3

def deltaA6SquareTerm : ℚ_[l.value] :=
  -(432 : ℚ_[l.value]) * (a6Value l) ^ 2

def deltaMixedTerm : ℚ_[l.value] :=
  (72 : ℚ_[l.value]) * a4Value l * a6Value l

def deltaCorrection : ℚ_[l.value] :=
  deltaSquareTerm l + deltaA4CubeTerm l + deltaA6SquareTerm l +
    deltaMixedTerm l

def deltaLeadingTerm : ℚ_[l.value] := -(a6Value l)

@[simp] theorem a4Value_eq : a4Value l =
    TateCurve.a4 ℚ_[l.value] (q l) := rfl

@[simp] theorem a6Value_eq : a6Value l =
    TateCurve.a6 ℚ_[l.value] (q l) := rfl

@[simp] theorem deltaValue_eq : deltaValue l = (canonicalCurve l).Δ := rfl

@[simp] theorem deltaSquareTerm_eq : deltaSquareTerm l =
    (TateCurve.a4 ℚ_[l.value] (q l)) ^ 2 := rfl

@[simp] theorem deltaA4CubeTerm_eq : deltaA4CubeTerm l =
    -(64 : ℚ_[l.value]) * (TateCurve.a4 ℚ_[l.value] (q l)) ^ 3 := rfl

@[simp] theorem deltaA6SquareTerm_eq : deltaA6SquareTerm l =
    -(432 : ℚ_[l.value]) * (TateCurve.a6 ℚ_[l.value] (q l)) ^ 2 := rfl

@[simp] theorem deltaMixedTerm_eq : deltaMixedTerm l =
    (72 : ℚ_[l.value]) * TateCurve.a4 ℚ_[l.value] (q l) *
      TateCurve.a6 ℚ_[l.value] (q l) := rfl

@[simp] theorem deltaLeadingTerm_eq : deltaLeadingTerm l =
    -(TateCurve.a6 ℚ_[l.value] (q l)) := rfl

theorem deltaCorrection_expanded : deltaCorrection l =
    (TateCurve.a4 ℚ_[l.value] (q l)) ^ 2 -
      64 * (TateCurve.a4 ℚ_[l.value] (q l)) ^ 3 -
      432 * (TateCurve.a6 ℚ_[l.value] (q l)) ^ 2 +
      72 * TateCurve.a4 ℚ_[l.value] (q l) *
        TateCurve.a6 ℚ_[l.value] (q l) := by
  simp only [deltaCorrection, deltaSquareTerm, deltaA4CubeTerm,
    deltaA6SquareTerm, deltaMixedTerm, a4Value, a6Value]
  ring

theorem deltaValue_expanded : deltaValue l =
    deltaSquareTerm l - a6Value l + deltaA4CubeTerm l +
      deltaA6SquareTerm l + deltaMixedTerm l := by
  rw [deltaValue_eq, canonicalCurve_delta]
  simp only [deltaSquareTerm, deltaA4CubeTerm, deltaA6SquareTerm,
    deltaMixedTerm, a4Value, a6Value]
  ring

theorem deltaValue_as_leading_plus_correction :
    deltaValue l = deltaLeadingTerm l + deltaCorrection l := by
  rw [deltaValue_expanded]
  simp only [deltaLeadingTerm, deltaCorrection, deltaA4CubeTerm,
    deltaA6SquareTerm, deltaMixedTerm]
  ring

theorem deltaValue_as_canonical_series : deltaValue l =
    (TateCurve.a4 ℚ_[l.value] (q l)) ^ 2 -
      TateCurve.a6 ℚ_[l.value] (q l) -
      64 * (TateCurve.a4 ℚ_[l.value] (q l)) ^ 3 -
      432 * (TateCurve.a6 ℚ_[l.value] (q l)) ^ 2 +
      72 * TateCurve.a4 ℚ_[l.value] (q l) *
        TateCurve.a6 ℚ_[l.value] (q l) := by
  exact canonicalCurve_delta l

end NamesAndDecompositions

section ConstantBounds

theorem norm_sixty_four_le_one :
    ‖(64 : ℚ_[l.value])‖ ≤ 1 :=
  nat_cast_norm_le_one l 64

theorem norm_four_hundred_thirty_two_le_one :
    ‖(432 : ℚ_[l.value])‖ ≤ 1 :=
  nat_cast_norm_le_one l 432

theorem norm_seventy_two_le_one :
    ‖(72 : ℚ_[l.value])‖ ≤ 1 :=
  nat_cast_norm_le_one l 72

theorem norm_sixty_four_nonneg :
    0 ≤ ‖(64 : ℚ_[l.value])‖ := norm_nonneg _

theorem norm_four_hundred_thirty_two_nonneg :
    0 ≤ ‖(432 : ℚ_[l.value])‖ := norm_nonneg _

theorem norm_seventy_two_nonneg :
    0 ≤ ‖(72 : ℚ_[l.value])‖ := norm_nonneg _

theorem norm_five_sq_le_one :
    ‖(5 : ℚ_[l.value])‖ ^ 2 ≤ 1 := by
  exact pow_le_one₀ (norm_nonneg _) (norm_five_le_one l)

theorem norm_five_cube_le_one :
    ‖(5 : ℚ_[l.value])‖ ^ 3 ≤ 1 := by
  exact pow_le_one₀ (norm_nonneg _) (norm_five_le_one l)

theorem q_norm_cube_lt_q_norm : ‖q l‖ ^ 3 < ‖q l‖ := by
  have hsq := q_norm_sq_lt_q_norm l
  have hqpos := q_norm_pos l
  have hmul : ‖q l‖ ^ 2 * ‖q l‖ < ‖q l‖ * ‖q l‖ :=
    mul_lt_mul_of_pos_right hsq hqpos
  have hlast : ‖q l‖ * ‖q l‖ < ‖q l‖ :=
    mul_lt_of_lt_one_left hqpos (q_norm_lt_one l)
  calc
    ‖q l‖ ^ 3 = ‖q l‖ ^ 2 * ‖q l‖ := by ring
    _ < ‖q l‖ * ‖q l‖ := hmul
    _ < ‖q l‖ := hlast

theorem q_norm_square_nonneg : 0 ≤ ‖q l‖ ^ 2 := sq_nonneg _

theorem q_norm_cube_nonneg : 0 ≤ ‖q l‖ ^ 3 := by positivity

theorem q_norm_square_le_q_norm : ‖q l‖ ^ 2 ≤ ‖q l‖ :=
  (q_norm_sq_lt_q_norm l).le

theorem q_norm_cube_le_q_norm : ‖q l‖ ^ 3 ≤ ‖q l‖ :=
  (q_norm_cube_lt_q_norm l).le

theorem q_norm_le_one : ‖q l‖ ≤ 1 := (q_norm_lt_one l).le

end ConstantBounds

section IndividualCorrectionBounds

theorem deltaSquareTerm_norm :
    ‖deltaSquareTerm l‖ = ‖a4Value l‖ ^ 2 := by
  rw [deltaSquareTerm, norm_pow]

theorem deltaA4CubeTerm_norm :
    ‖deltaA4CubeTerm l‖ = ‖(64 : ℚ_[l.value])‖ * ‖a4Value l‖ ^ 3 := by
  simp [deltaA4CubeTerm, norm_mul, norm_pow]

theorem deltaA6SquareTerm_norm :
    ‖deltaA6SquareTerm l‖ = ‖(432 : ℚ_[l.value])‖ * ‖a6Value l‖ ^ 2 := by
  simp [deltaA6SquareTerm, norm_mul, norm_pow]

theorem deltaMixedTerm_norm :
    ‖deltaMixedTerm l‖ = ‖(72 : ℚ_[l.value])‖ *
      ‖a4Value l‖ * ‖a6Value l‖ := by
  rw [deltaMixedTerm, norm_mul, norm_mul]

theorem a4Value_norm : ‖a4Value l‖ =
    ‖(5 : ℚ_[l.value])‖ * ‖q l‖ := by
  exact a4_norm_eq l

theorem a6Value_norm : ‖a6Value l‖ = ‖q l‖ := by
  exact a6_norm_eq l

theorem deltaSquareTerm_norm_le_q_square :
    ‖deltaSquareTerm l‖ ≤ ‖q l‖ ^ 2 := by
  rw [deltaSquareTerm_norm, a4Value_norm]
  calc
    (‖(5 : ℚ_[l.value])‖ * ‖q l‖) ^ 2 =
        ‖(5 : ℚ_[l.value])‖ ^ 2 * ‖q l‖ ^ 2 := by ring
    _ ≤ 1 * ‖q l‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right (norm_five_sq_le_one l)
        (q_norm_square_nonneg l)
    _ = ‖q l‖ ^ 2 := one_mul _

theorem deltaA4CubeTerm_norm_le_q_cube :
    ‖deltaA4CubeTerm l‖ ≤ ‖q l‖ ^ 3 := by
  rw [deltaA4CubeTerm_norm, a4Value_norm]
  calc
    ‖(64 : ℚ_[l.value])‖ *
        (‖(5 : ℚ_[l.value])‖ * ‖q l‖) ^ 3 =
      ‖(64 : ℚ_[l.value])‖ * ‖(5 : ℚ_[l.value])‖ ^ 3 *
        ‖q l‖ ^ 3 := by ring
    _ ≤ 1 * ‖q l‖ ^ 3 := by
      have hcoef : ‖(64 : ℚ_[l.value])‖ *
          ‖(5 : ℚ_[l.value])‖ ^ 3 ≤ 1 := by
        calc
          ‖(64 : ℚ_[l.value])‖ * ‖(5 : ℚ_[l.value])‖ ^ 3 ≤
              ‖(64 : ℚ_[l.value])‖ * 1 := by
            exact mul_le_mul_of_nonneg_left (norm_five_cube_le_one l)
              (norm_nonneg _)
          _ ≤ 1 * 1 := by
            exact mul_le_mul_of_nonneg_right (norm_sixty_four_le_one l)
              (by norm_num)
          _ = 1 := by norm_num
      exact mul_le_mul_of_nonneg_right hcoef (q_norm_cube_nonneg l)
    _ = ‖q l‖ ^ 3 := one_mul _

theorem deltaA6SquareTerm_norm_le_q_square :
    ‖deltaA6SquareTerm l‖ ≤ ‖q l‖ ^ 2 := by
  rw [deltaA6SquareTerm_norm, a6Value_norm]
  exact mul_le_of_le_one_left (sq_nonneg _) (norm_four_hundred_thirty_two_le_one l)

theorem deltaMixedTerm_norm_le_q_square :
    ‖deltaMixedTerm l‖ ≤ ‖q l‖ ^ 2 := by
  rw [deltaMixedTerm_norm, a4Value_norm, a6Value_norm]
  calc
    ‖(72 : ℚ_[l.value])‖ *
        (‖(5 : ℚ_[l.value])‖ * ‖q l‖) * ‖q l‖ =
      (‖(72 : ℚ_[l.value])‖ * ‖(5 : ℚ_[l.value])‖) *
        ‖q l‖ ^ 2 := by ring
    _ ≤ 1 * ‖q l‖ ^ 2 := by
      have hcoef : ‖(72 : ℚ_[l.value])‖ *
          ‖(5 : ℚ_[l.value])‖ ≤ 1 := by
        calc
          ‖(72 : ℚ_[l.value])‖ * ‖(5 : ℚ_[l.value])‖ ≤
              ‖(72 : ℚ_[l.value])‖ * 1 := by
            exact mul_le_mul_of_nonneg_left (norm_five_le_one l)
              (norm_nonneg _)
          _ ≤ 1 * 1 := by
            exact mul_le_mul_of_nonneg_right (norm_seventy_two_le_one l)
              (by norm_num)
          _ = 1 := by norm_num
      exact mul_le_mul_of_nonneg_right hcoef (q_norm_square_nonneg l)
    _ = ‖q l‖ ^ 2 := one_mul _

theorem deltaSquareTerm_norm_lt_leading :
    ‖deltaSquareTerm l‖ < ‖a6Value l‖ := by
  rw [a6Value_norm]
  exact (deltaSquareTerm_norm_le_q_square l).trans_lt (q_norm_sq_lt_q_norm l)

theorem deltaA4CubeTerm_norm_lt_leading :
    ‖deltaA4CubeTerm l‖ < ‖a6Value l‖ := by
  rw [a6Value_norm]
  exact (deltaA4CubeTerm_norm_le_q_cube l).trans_lt (q_norm_cube_lt_q_norm l)

theorem deltaA6SquareTerm_norm_lt_leading :
    ‖deltaA6SquareTerm l‖ < ‖a6Value l‖ := by
  rw [a6Value_norm]
  exact (deltaA6SquareTerm_norm_le_q_square l).trans_lt (q_norm_sq_lt_q_norm l)

theorem deltaMixedTerm_norm_lt_leading :
    ‖deltaMixedTerm l‖ < ‖a6Value l‖ := by
  rw [a6Value_norm]
  exact (deltaMixedTerm_norm_le_q_square l).trans_lt (q_norm_sq_lt_q_norm l)

end IndividualCorrectionBounds

section CorrectionAggregation

theorem deltaCorrection_norm_le_max_first_two :
    ‖deltaSquareTerm l + deltaA4CubeTerm l‖ ≤
      max ‖deltaSquareTerm l‖ ‖deltaA4CubeTerm l‖ := by
  exact Padic.nonarchimedean _ _

theorem deltaCorrection_norm_le_max_last_two :
    ‖deltaA6SquareTerm l + deltaMixedTerm l‖ ≤
      max ‖deltaA6SquareTerm l‖ ‖deltaMixedTerm l‖ := by
  exact Padic.nonarchimedean _ _

theorem deltaCorrection_norm_le_nested_max :
    ‖deltaCorrection l‖ ≤
      max (max ‖deltaSquareTerm l‖ ‖deltaA4CubeTerm l‖)
        (max ‖deltaA6SquareTerm l‖ ‖deltaMixedTerm l‖) := by
  rw [deltaCorrection]
  have h₁ := Padic.nonarchimedean (p := l.value)
    (deltaSquareTerm l + deltaA4CubeTerm l)
    (deltaA6SquareTerm l + deltaMixedTerm l)
  have h₂ := deltaCorrection_norm_le_max_first_two l
  have h₃ := deltaCorrection_norm_le_max_last_two l
  calc
    ‖deltaSquareTerm l + deltaA4CubeTerm l + deltaA6SquareTerm l +
        deltaMixedTerm l‖ =
        ‖(deltaSquareTerm l + deltaA4CubeTerm l) +
          (deltaA6SquareTerm l + deltaMixedTerm l)‖ := by
      congr 1
      ring
    _ ≤ max ‖deltaSquareTerm l + deltaA4CubeTerm l‖
          ‖deltaA6SquareTerm l + deltaMixedTerm l‖ := h₁
    _ ≤ max (max ‖deltaSquareTerm l‖ ‖deltaA4CubeTerm l‖)
        (max ‖deltaA6SquareTerm l‖ ‖deltaMixedTerm l‖) := by
      exact max_le_max h₂ h₃

theorem deltaCorrection_norm_lt_leading :
    ‖deltaCorrection l‖ < ‖a6Value l‖ := by
  apply lt_of_le_of_lt (deltaCorrection_norm_le_nested_max l)
  apply max_lt
  · exact max_lt (deltaSquareTerm_norm_lt_leading l)
      (deltaA4CubeTerm_norm_lt_leading l)
  · exact max_lt (deltaA6SquareTerm_norm_lt_leading l)
      (deltaMixedTerm_norm_lt_leading l)

theorem deltaCorrection_norm_lt_q :
    ‖deltaCorrection l‖ < ‖q l‖ := by
  calc
    ‖deltaCorrection l‖ < ‖a6Value l‖ :=
      deltaCorrection_norm_lt_leading l
    _ = ‖q l‖ := a6Value_norm l

theorem deltaCorrection_norm_nonneg : 0 ≤ ‖deltaCorrection l‖ := norm_nonneg _

theorem deltaLeadingTerm_norm : ‖deltaLeadingTerm l‖ = ‖q l‖ := by
  rw [deltaLeadingTerm, norm_neg, a6Value_norm]

theorem deltaLeadingTerm_ne_zero : deltaLeadingTerm l ≠ 0 := by
  rw [deltaLeadingTerm]
  exact neg_ne_zero.mpr (a6_ne_zero l)

theorem deltaCorrection_ne_leading_norm :
    ‖deltaCorrection l‖ ≠ ‖deltaLeadingTerm l‖ := by
  rw [deltaLeadingTerm_norm]
  exact ne_of_lt (deltaCorrection_norm_lt_q l)

theorem deltaCorrection_is_strict_error :
    ‖deltaCorrection l‖ < ‖deltaLeadingTerm l‖ := by
  rw [deltaLeadingTerm_norm]
  exact deltaCorrection_norm_lt_q l

end CorrectionAggregation

section DiscriminantClosure

theorem deltaValue_norm_eq_leading : ‖deltaValue l‖ = ‖q l‖ := by
  rw [deltaValue_as_leading_plus_correction l]
  rw [Padic.add_eq_max_of_ne (deltaCorrection_ne_leading_norm l).symm]
  rw [max_eq_left (deltaCorrection_is_strict_error l).le]
  exact deltaLeadingTerm_norm l

theorem deltaValue_norm_eq_a6 : ‖deltaValue l‖ = ‖a6Value l‖ := by
  rw [deltaValue_norm_eq_leading, a6Value_norm]

theorem deltaValue_norm_pos : 0 < ‖deltaValue l‖ := by
  rw [deltaValue_norm_eq_leading]
  exact q_norm_pos l

theorem deltaValue_ne_zero : deltaValue l ≠ 0 := by
  intro h
  have hn := deltaValue_norm_pos l
  rw [h, norm_zero] at hn
  exact (lt_irrefl (0 : ℝ)) hn

theorem canonicalCurve_delta_ne_zero : (canonicalCurve l).Δ ≠ 0 := by
  simpa [deltaValue] using deltaValue_ne_zero l

theorem canonicalCurve_is_elliptic : (canonicalCurve l).IsElliptic := by
  exact canonicalCurve_is_elliptic_of_delta_ne_zero l
    (canonicalCurve_delta_ne_zero l)

theorem discriminantNonzeroObligation_proved : discriminantNonzeroObligation l := by
  simpa [discriminantNonzeroObligation, deltaValue] using canonicalCurve_delta_ne_zero l

theorem canonicalCurve_delta_is_unit : IsUnit (canonicalCurve l).Δ := by
  exact isUnit_iff_ne_zero.mpr (canonicalCurve_delta_ne_zero l)

theorem canonicalCurve_delta_is_nonzero_and_elliptic :
    (canonicalCurve l).Δ ≠ 0 ∧ (canonicalCurve l).IsElliptic :=
  ⟨canonicalCurve_delta_ne_zero l, canonicalCurve_is_elliptic l⟩

theorem canonicalCurve_delta_norm_eq_q :
    ‖(canonicalCurve l).Δ‖ = ‖q l‖ := by
  simpa [deltaValue] using deltaValue_norm_eq_leading l

theorem canonicalCurve_delta_norm_lt_one :
    ‖(canonicalCurve l).Δ‖ < 1 := by
  rw [canonicalCurve_delta_norm_eq_q]
  exact q_norm_lt_one l

theorem canonicalCurve_delta_norm_le_one :
    ‖(canonicalCurve l).Δ‖ ≤ 1 :=
  (canonicalCurve_delta_norm_lt_one l).le

theorem canonicalCurve_delta_is_integral_element :
    ∃ d : ℤ_[l.value], (d : ℚ_[l.value]) = (canonicalCurve l).Δ := by
  refine ⟨integralElement l (canonicalCurve l).Δ
    (canonicalCurve_delta_norm_le_one l), ?_⟩
  rfl

def integralDelta : ℤ_[l.value] :=
  integralElement l (canonicalCurve l).Δ
    (canonicalCurve_delta_norm_le_one l)

@[simp] theorem coe_integralDelta :
    (integralDelta l : ℚ_[l.value]) = (canonicalCurve l).Δ := rfl

theorem integralDelta_norm : ‖integralDelta l‖ = ‖q l‖ := by
  rw [integralDelta, integralElement_norm]
  · exact canonicalCurve_delta_norm_eq_q l

theorem integralDelta_mem_nonunits :
    integralDelta l ∈ nonunits ℤ_[l.value] := by
  rw [PadicInt.mem_nonunits, integralDelta_norm]
  exact q_norm_lt_one l

theorem integralDelta_in_maximalIdeal :
    integralDelta l ∈ IsLocalRing.maximalIdeal ℤ_[l.value] := by
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  rw [integralDelta_norm]
  exact q_norm_lt_one l

theorem integralDelta_is_nonzero : (integralDelta l : ℚ_[l.value]) ≠ 0 := by
  rw [coe_integralDelta]
  exact canonicalCurve_delta_ne_zero l

theorem integralDelta_has_nonzero_generic_fiber :
    ∃ d : ℤ_[l.value], (d : ℚ_[l.value]) ≠ 0 ∧
      (d : ℚ_[l.value]) = (canonicalCurve l).Δ := by
  exact ⟨integralDelta l, integralDelta_is_nonzero l, rfl⟩

theorem discriminant_is_strictly_smaller_than_one_but_nonzero :
    (canonicalCurve l).Δ ≠ 0 ∧ ‖(canonicalCurve l).Δ‖ < 1 :=
  ⟨canonicalCurve_delta_ne_zero l, canonicalCurve_delta_norm_lt_one l⟩

theorem discriminant_is_not_a_unit_in_the_integral_model :
    integralDelta l ∈ nonunits ℤ_[l.value] :=
  integralDelta_mem_nonunits l

end DiscriminantClosure

section StableApiConsequences

theorem canonicalCurve_elliptic_iff_discriminant :
    (canonicalCurve l).IsElliptic ↔ (canonicalCurve l).Δ ≠ 0 :=
  canonicalCurve_is_elliptic_iff_delta_ne_zero l

theorem canonicalCurve_elliptic_of_q_parameter :
    (canonicalCurve l).IsElliptic := canonicalCurve_is_elliptic l

theorem canonicalCurve_c4_unit_and_delta_nonzero :
    IsUnit (canonicalCurve l).c₄ ∧ (canonicalCurve l).Δ ≠ 0 :=
  ⟨canonicalCurve_c4_unit l, canonicalCurve_delta_ne_zero l⟩

theorem canonicalCurve_coefficients_and_discriminant_packet :
    TateCurve.a4 ℚ_[l.value] (q l) ≠ 0 ∧
      TateCurve.a6 ℚ_[l.value] (q l) ≠ 0 ∧
      (canonicalCurve l).c₄ ≠ 0 ∧
      (canonicalCurve l).Δ ≠ 0 :=
  ⟨a4_ne_zero l, a6_ne_zero l, canonicalCurve_c4_nonzero l,
    canonicalCurve_delta_ne_zero l⟩

theorem canonicalCurve_norm_packet :
    ‖TateCurve.a4 ℚ_[l.value] (q l)‖ =
        ‖(5 : ℚ_[l.value])‖ * ‖q l‖ ∧
      ‖TateCurve.a6 ℚ_[l.value] (q l)‖ = ‖q l‖ ∧
      ‖(canonicalCurve l).c₄‖ = 1 ∧
      ‖(canonicalCurve l).Δ‖ = ‖q l‖ :=
  ⟨a4_norm_eq l, a6_norm_eq l, c4_norm_eq_one l,
    canonicalCurve_delta_norm_eq_q l⟩

theorem canonicalCurve_q_series_output :
    (canonicalCurve l).IsElliptic ∧
      (canonicalCurve l).Δ ≠ 0 ∧
      ‖(canonicalCurve l).Δ‖ = ‖q l‖ ∧
      IsUnit (canonicalCurve l).c₄ := by
  exact ⟨canonicalCurve_is_elliptic l,
    canonicalCurve_delta_ne_zero l,
    canonicalCurve_delta_norm_eq_q l,
    canonicalCurve_c4_unit l⟩

theorem canonicalCurve_q_series_output_reusable :
    (canonicalCurve l).IsElliptic ∧
      ‖(canonicalCurve l).Δ‖ < 1 ∧
      ‖(canonicalCurve l).c₄‖ = 1 := by
  exact ⟨canonicalCurve_is_elliptic l,
    canonicalCurve_delta_norm_lt_one l,
    c4_norm_eq_one l⟩

theorem discriminant_obligation_is_no_longer_open :
    discriminantNonzeroObligation l :=
  discriminantNonzeroObligation_proved l

end StableApiConsequences

section GeneralNonarchimedeanCertificates

theorem norm_add_of_strict_error {x y : ℚ_[l.value]}
    (hy : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  have hne : ‖x‖ ≠ ‖y‖ := ne_of_gt hy
  rw [Padic.add_eq_max_of_ne hne, max_eq_left hy.le]

theorem norm_sub_of_strict_error {x y : ℚ_[l.value]}
    (hy : ‖y‖ < ‖x‖) : ‖x - y‖ = ‖x‖ := by
  have hneg : ‖-y‖ < ‖x‖ := by simpa using hy
  simpa [sub_eq_add_neg] using
    (norm_add_of_strict_error l (x := x) (y := -y) hneg)

theorem norm_add_of_strict_error_eq_left {x y : ℚ_[l.value]}
    (hy : ‖y‖ < ‖x‖) : ‖y + x‖ = ‖x‖ := by
  simpa [add_comm] using norm_add_of_strict_error l hy

theorem norm_sub_of_strict_error_eq_left {x y : ℚ_[l.value]}
    (hy : ‖y‖ < ‖x‖) : ‖y - x‖ = ‖x‖ := by
  calc
    ‖y - x‖ = ‖-(x - y)‖ := by congr 1; ring
    _ = ‖x - y‖ := norm_neg _
    _ = ‖x‖ := norm_sub_of_strict_error l hy

theorem norm_add_le_max_four {w x y z : ℚ_[l.value]} :
    ‖w + x + y + z‖ ≤
      max (max ‖w‖ ‖x‖) (max ‖y‖ ‖z‖) := by
  have h₁ : ‖w + x‖ ≤ max ‖w‖ ‖x‖ := Padic.nonarchimedean _ _
  have h₂ : ‖y + z‖ ≤ max ‖y‖ ‖z‖ := Padic.nonarchimedean _ _
  have h₃ : ‖(w + x) + (y + z)‖ ≤
      max ‖w + x‖ ‖y + z‖ := Padic.nonarchimedean _ _
  calc
    ‖w + x + y + z‖ = ‖(w + x) + (y + z)‖ := by congr 1; ring
    _ ≤ max ‖w + x‖ ‖y + z‖ := h₃
    _ ≤ max (max ‖w‖ ‖x‖) (max ‖y‖ ‖z‖) := max_le_max h₁ h₂

theorem norm_add_four_of_each_strict {w x y z a : ℚ_[l.value]}
    (hw : ‖w‖ < ‖a‖) (hx : ‖x‖ < ‖a‖)
    (hy : ‖y‖ < ‖a‖) (hz : ‖z‖ < ‖a‖) :
    ‖w + x + y + z‖ < ‖a‖ := by
  apply lt_of_le_of_lt (norm_add_le_max_four l)
  apply max_lt
  · exact max_lt hw hx
  · exact max_lt hy hz

theorem norm_neg_eq_norm {x : ℚ_[l.value]} : ‖-x‖ = ‖x‖ := norm_neg _

theorem norm_smul_nat_le {n : ℕ} {x : ℚ_[l.value]}
    (hn : ‖(n : ℚ_[l.value])‖ ≤ 1) :
    ‖(n : ℚ_[l.value]) * x‖ ≤ ‖x‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg (x : ℚ_[l.value])) hn

theorem norm_power_mul_le {n m : ℕ} {x : ℚ_[l.value]}
    (hn : ‖(n : ℚ_[l.value])‖ ^ m ≤ 1) :
    ‖(n : ℚ_[l.value]) ^ m * x‖ ≤ ‖x‖ := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg (x : ℚ_[l.value])) hn

theorem norm_q_power_mul_le {n m : ℕ} (hn : ‖(n : ℚ_[l.value])‖ ^ m ≤ 1) :
    ‖(n : ℚ_[l.value]) ^ m * q l ^ 2‖ ≤ ‖q l‖ ^ 2 := by
  rw [norm_mul, norm_pow, norm_pow]
  simpa using mul_le_mul_of_nonneg_right hn (q_norm_square_nonneg l)

theorem q_norm_pow_lt_q_norm {m : ℕ} (hm : 2 ≤ m) :
    ‖q l‖ ^ m < ‖q l‖ := by
  exact lt_of_le_of_lt (q_norm_pow_monotone_from_two l hm)
    (q_norm_sq_lt_q_norm l)

theorem q_norm_pow_strictly_positive {m : ℕ} :
    0 < ‖q l‖ ^ m := by
  exact pow_pos (q_norm_pos l) _

theorem q_norm_pow_nonzero {m : ℕ} : ‖q l‖ ^ m ≠ 0 :=
  ne_of_gt (q_norm_pow_strictly_positive l)

theorem correction_is_small_relative_to_any_power_one_leading
    {x : ℚ_[l.value]} (hx : ‖x‖ = ‖q l‖)
    {w y z t : ℚ_[l.value]}
    (hw : ‖w‖ < ‖x‖) (hy : ‖y‖ < ‖x‖)
    (hz : ‖z‖ < ‖x‖) (ht : ‖t‖ < ‖x‖) :
    ‖w + y + z + t‖ < ‖q l‖ := by
  rw [← hx]
  exact norm_add_four_of_each_strict l hw hy hz ht

end GeneralNonarchimedeanCertificates

section IntegralDiscriminantTransport

def integralCurveDelta : ℤ_[l.value] := (integralCurve l).Δ

@[simp] theorem integralCurveDelta_eq : integralCurveDelta l =
    (integralCurve l).Δ := rfl

theorem integralCurveDelta_cast :
    (integralCurveDelta l : ℚ_[l.value]) = (canonicalCurve l).Δ := by
  have h := congrArg (fun W : WeierstrassCurve ℚ_[l.value] => W.Δ)
    (integralCurveMap_eq_canonical l)
  simpa [integralCurveMap, integralCurveDelta, WeierstrassCurve.map_Δ] using h

theorem integralCurveDelta_cast_eq_deltaValue :
    (integralCurveDelta l : ℚ_[l.value]) = deltaValue l := by
  simpa [deltaValue] using integralCurveDelta_cast l

theorem integralCurveDelta_norm : ‖integralCurveDelta l‖ = ‖q l‖ := by
  change ‖(integralCurveDelta l : ℚ_[l.value])‖ = ‖q l‖
  rw [integralCurveDelta_cast]
  exact canonicalCurve_delta_norm_eq_q l

theorem integralCurveDelta_norm_lt_one : ‖integralCurveDelta l‖ < 1 := by
  rw [integralCurveDelta_norm]
  exact q_norm_lt_one l

theorem integralCurveDelta_mem_maximalIdeal :
    integralCurveDelta l ∈ IsLocalRing.maximalIdeal ℤ_[l.value] := by
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits,
    integralCurveDelta_norm]
  exact q_norm_lt_one l

theorem integralCurveDelta_residue_zero :
    IsLocalRing.residue ℤ_[l.value] (integralCurveDelta l) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact integralCurveDelta_mem_maximalIdeal l

theorem integralCurveDelta_cast_ne_zero :
    (integralCurveDelta l : ℚ_[l.value]) ≠ 0 := by
  rw [integralCurveDelta_cast]
  exact canonicalCurve_delta_ne_zero l

theorem integralCurveDelta_ne_zero : integralCurveDelta l ≠ 0 := by
  intro h
  have hc := congrArg (fun z : ℤ_[l.value] => (z : ℚ_[l.value])) h
  exact integralCurveDelta_cast_ne_zero l hc

theorem integralCurveDelta_is_nonunit :
    integralCurveDelta l ∈ nonunits ℤ_[l.value] := by
  rw [PadicInt.mem_nonunits, integralCurveDelta_norm]
  exact q_norm_lt_one l

theorem integralCurveDelta_is_not_zero_in_residue_and_generic
    : integralCurveDelta l ≠ 0 ∧
      IsLocalRing.residue ℤ_[l.value] (integralCurveDelta l) = 0 ∧
      (integralCurveDelta l : ℚ_[l.value]) ≠ 0 :=
  ⟨integralCurveDelta_ne_zero l, integralCurveDelta_residue_zero l,
    integralCurveDelta_cast_ne_zero l⟩

theorem canonicalCurve_is_integral :
    WeierstrassCurve.IsIntegral (ℤ_[l.value]) (canonicalCurve l) := by
  rcases canonicalCurve_has_integral_presentation l with ⟨W, hW⟩
  exact ⟨⟨W, hW.symm⟩⟩

theorem integralCurve_is_integral :
    WeierstrassCurve.IsIntegral (ℤ_[l.value]) (integralCurveMap l) := by
  exact ⟨⟨integralCurve l, rfl⟩⟩

theorem integralCurve_delta_cast_is_canonical :
    algebraMap (ℤ_[l.value]) (ℚ_[l.value]) (integralCurve l).Δ =
      (canonicalCurve l).Δ := by
  simpa [integralCurveDelta] using integralCurveDelta_cast l

theorem integralCurve_delta_cast_is_deltaValue :
    algebraMap (ℤ_[l.value]) (ℚ_[l.value]) (integralCurve l).Δ =
      deltaValue l := by
  simpa [integralCurveDelta] using integralCurveDelta_cast_eq_deltaValue l

theorem integralCurve_delta_is_nonzero_after_map :
    algebraMap (ℤ_[l.value]) (ℚ_[l.value]) (integralCurve l).Δ ≠ 0 := by
  rw [integralCurve_delta_cast_is_canonical]
  exact canonicalCurve_delta_ne_zero l

theorem integralCurve_c4_residue_ne_zero :
    IsLocalRing.residue ℤ_[l.value] (integralCurve l).c₄ ≠ 0 := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit (integralCurve l).c₄).2
  exact integralPresentation_c4_is_unit l

theorem integralCurve_delta_residue_zero :
    IsLocalRing.residue ℤ_[l.value] (integralCurve l).Δ = 0 := by
  exact integralCurveDelta_residue_zero l

theorem integralCurve_reduction_data_packet :
    (IsLocalRing.residue ℤ_[l.value] (integralCurve l).Δ = 0) ∧
      (IsLocalRing.residue ℤ_[l.value] (integralCurve l).c₄ ≠ 0) ∧
      algebraMap (ℤ_[l.value]) (ℚ_[l.value]) (integralCurve l).Δ ≠ 0 :=
  ⟨integralCurve_delta_residue_zero l, integralCurve_c4_residue_ne_zero l,
    integralCurve_delta_is_nonzero_after_map l⟩

structure IntegralDiscriminantPacket where
  curve : WeierstrassCurve ℤ_[l.value]
  curve_eq : curve = integralCurve l
  delta_cast : algebraMap (ℤ_[l.value]) (ℚ_[l.value]) curve.Δ =
    (canonicalCurve l).Δ
  delta_nonzero : curve.Δ ≠ 0
  delta_nonunit : curve.Δ ∈ nonunits ℤ_[l.value]
  c4_unit : IsUnit curve.c₄

def integralDiscriminantPacket : IntegralDiscriminantPacket l :=
  { curve := integralCurve l
    curve_eq := rfl
    delta_cast := integralCurve_delta_cast_is_canonical l
    delta_nonzero := by
      intro h
      apply integralCurve_delta_is_nonzero_after_map l
      rw [h]
      simp
    delta_nonunit := by
      exact integralCurveDelta_is_nonunit l
    c4_unit := integralPresentation_c4_is_unit l }

theorem integralDiscriminantPacket_curve :
    (integralDiscriminantPacket l).curve = integralCurve l := rfl

theorem integralDiscriminantPacket_delta_cast :
    algebraMap (ℤ_[l.value]) (ℚ_[l.value])
        (integralDiscriminantPacket l).curve.Δ =
      (canonicalCurve l).Δ :=
  (integralDiscriminantPacket l).delta_cast

theorem integralDiscriminantPacket_delta_nonzero :
    (integralDiscriminantPacket l).curve.Δ ≠ 0 :=
  (integralDiscriminantPacket l).delta_nonzero

theorem integralDiscriminantPacket_delta_nonunit :
    (integralDiscriminantPacket l).curve.Δ ∈ nonunits ℤ_[l.value] :=
  (integralDiscriminantPacket l).delta_nonunit

theorem integralDiscriminantPacket_c4_unit :
    IsUnit (integralDiscriminantPacket l).curve.c₄ :=
  (integralDiscriminantPacket l).c4_unit

end IntegralDiscriminantTransport

section DeltaDominanceStructures

structure StrictDominanceCertificate (x y : ℚ_[l.value]) where
  error_lt : ‖y‖ < ‖x‖
  sum_norm : ‖x + y‖ = ‖x‖
  sum_ne_zero : x + y ≠ 0

theorem strictDominanceCertificate {x y : ℚ_[l.value]}
    (hy : ‖y‖ < ‖x‖) : StrictDominanceCertificate l x y :=
  { error_lt := hy
    sum_norm := norm_add_of_strict_error l hy
    sum_ne_zero := by
      intro h
      have hxne : x ≠ 0 := by
        intro hx
        rw [hx, norm_zero] at hy
        exact (not_lt_of_ge (norm_nonneg y)) hy
      have hnorm := norm_add_of_strict_error l hy
      rw [h, norm_zero] at hnorm
      exact (ne_of_gt (norm_pos_iff.mpr hxne)) hnorm.symm }

theorem strictDominanceCertificate_error_lt {x y : ℚ_[l.value]}
    (hy : ‖y‖ < ‖x‖) :
    ‖y‖ < ‖x‖ := (strictDominanceCertificate l hy).error_lt

theorem strictDominanceCertificate_sum_norm {x y : ℚ_[l.value]}
    (hy : ‖y‖ < ‖x‖) :
    ‖x + y‖ = ‖x‖ := (strictDominanceCertificate l hy).sum_norm

theorem strictDominanceCertificate_sum_ne_zero {x y : ℚ_[l.value]}
    (hy : ‖y‖ < ‖x‖) : x + y ≠ 0 :=
  (strictDominanceCertificate l hy).sum_ne_zero

theorem discriminantDominanceCertificate :
    StrictDominanceCertificate l (deltaLeadingTerm l) (deltaCorrection l) :=
  strictDominanceCertificate l (deltaCorrection_is_strict_error l)

theorem discriminantDominanceCertificate_error_lt :
    ‖deltaCorrection l‖ < ‖deltaLeadingTerm l‖ :=
  (discriminantDominanceCertificate l).error_lt

theorem discriminantDominanceCertificate_sum_norm :
    ‖deltaLeadingTerm l + deltaCorrection l‖ =
      ‖deltaLeadingTerm l‖ :=
  (discriminantDominanceCertificate l).sum_norm

theorem discriminantDominanceCertificate_sum_ne_zero :
    deltaLeadingTerm l + deltaCorrection l ≠ 0 :=
  (discriminantDominanceCertificate l).sum_ne_zero

structure CanonicalDiscriminantOutput where
  discriminant : ℚ_[l.value]
  discriminant_eq : discriminant = deltaValue l
  nonzero : discriminant ≠ 0
  norm_eq_q : ‖discriminant‖ = ‖q l‖
  elliptic : (canonicalCurve l).IsElliptic
  c4_unit : IsUnit (canonicalCurve l).c₄

def canonicalDiscriminantOutput : CanonicalDiscriminantOutput l :=
  { discriminant := deltaValue l
    discriminant_eq := rfl
    nonzero := deltaValue_ne_zero l
    norm_eq_q := deltaValue_norm_eq_leading l
    elliptic := canonicalCurve_is_elliptic l
    c4_unit := canonicalCurve_c4_unit l }

theorem canonicalDiscriminantOutput_discriminant :
    (canonicalDiscriminantOutput l).discriminant = deltaValue l := rfl

theorem canonicalDiscriminantOutput_nonzero :
    (canonicalDiscriminantOutput l).discriminant ≠ 0 :=
  (canonicalDiscriminantOutput l).nonzero

theorem canonicalDiscriminantOutput_norm :
    ‖(canonicalDiscriminantOutput l).discriminant‖ = ‖q l‖ :=
  (canonicalDiscriminantOutput l).norm_eq_q

theorem canonicalDiscriminantOutput_elliptic :
    (canonicalCurve l).IsElliptic :=
  (canonicalDiscriminantOutput l).elliptic

theorem canonicalDiscriminantOutput_c4_unit :
    IsUnit (canonicalCurve l).c₄ :=
  (canonicalDiscriminantOutput l).c4_unit

end DeltaDominanceStructures

section ConsumerFacingOutput

structure DeltaCorrectionNormPacket where
  squareNorm : ℝ
  cubeNorm : ℝ
  squareA6Norm : ℝ
  mixedNorm : ℝ
  leadingNorm : ℝ
  square_lt : squareNorm < leadingNorm
  cube_lt : cubeNorm < leadingNorm
  squareA6_lt : squareA6Norm < leadingNorm
  mixed_lt : mixedNorm < leadingNorm
  correction_lt : ‖deltaCorrection l‖ < leadingNorm

def deltaCorrectionNormPacket : DeltaCorrectionNormPacket l :=
  { squareNorm := ‖deltaSquareTerm l‖
    cubeNorm := ‖deltaA4CubeTerm l‖
    squareA6Norm := ‖deltaA6SquareTerm l‖
    mixedNorm := ‖deltaMixedTerm l‖
    leadingNorm := ‖deltaLeadingTerm l‖
    square_lt := by
      calc
        ‖deltaSquareTerm l‖ < ‖a6Value l‖ :=
          deltaSquareTerm_norm_lt_leading l
        _ = ‖deltaLeadingTerm l‖ := by
          rw [deltaLeadingTerm_norm, a6Value_norm]
    cube_lt := by
      calc
        ‖deltaA4CubeTerm l‖ < ‖a6Value l‖ :=
          deltaA4CubeTerm_norm_lt_leading l
        _ = ‖deltaLeadingTerm l‖ := by
          rw [deltaLeadingTerm_norm, a6Value_norm]
    squareA6_lt := by
      calc
        ‖deltaA6SquareTerm l‖ < ‖a6Value l‖ :=
          deltaA6SquareTerm_norm_lt_leading l
        _ = ‖deltaLeadingTerm l‖ := by
          rw [deltaLeadingTerm_norm, a6Value_norm]
    mixed_lt := by
      calc
        ‖deltaMixedTerm l‖ < ‖a6Value l‖ :=
          deltaMixedTerm_norm_lt_leading l
        _ = ‖deltaLeadingTerm l‖ := by
          rw [deltaLeadingTerm_norm, a6Value_norm]
    correction_lt := by
      calc
        ‖deltaCorrection l‖ < ‖a6Value l‖ :=
          deltaCorrection_norm_lt_leading l
        _ = ‖deltaLeadingTerm l‖ := by
          rw [deltaLeadingTerm_norm, a6Value_norm] }

theorem deltaCorrectionNormPacket_square_lt :
    (deltaCorrectionNormPacket l).squareNorm <
      (deltaCorrectionNormPacket l).leadingNorm :=
  (deltaCorrectionNormPacket l).square_lt

theorem deltaCorrectionNormPacket_cube_lt :
    (deltaCorrectionNormPacket l).cubeNorm <
      (deltaCorrectionNormPacket l).leadingNorm :=
  (deltaCorrectionNormPacket l).cube_lt

theorem deltaCorrectionNormPacket_squareA6_lt :
    (deltaCorrectionNormPacket l).squareA6Norm <
      (deltaCorrectionNormPacket l).leadingNorm :=
  (deltaCorrectionNormPacket l).squareA6_lt

theorem deltaCorrectionNormPacket_mixed_lt :
    (deltaCorrectionNormPacket l).mixedNorm <
      (deltaCorrectionNormPacket l).leadingNorm :=
  (deltaCorrectionNormPacket l).mixed_lt

theorem deltaCorrectionNormPacket_correction_lt :
    ‖deltaCorrection l‖ <
      (deltaCorrectionNormPacket l).leadingNorm :=
  (deltaCorrectionNormPacket l).correction_lt

theorem deltaCorrectionNormPacket_leading_norm :
    (deltaCorrectionNormPacket l).leadingNorm = ‖q l‖ := by
  change ‖deltaLeadingTerm l‖ = ‖q l‖
  exact deltaLeadingTerm_norm l

structure CanonicalEllipticityPacket where
  curve : WeierstrassCurve ℚ_[l.value]
  curve_eq : curve = canonicalCurve l
  a4_nonzero : curve.a₄ ≠ 0
  a6_nonzero : curve.a₆ ≠ 0
  c4_unit : IsUnit curve.c₄
  delta_nonzero : curve.Δ ≠ 0
  delta_norm : ‖curve.Δ‖ = ‖q l‖
  elliptic : curve.IsElliptic

def canonicalEllipticityPacket : CanonicalEllipticityPacket l :=
  { curve := canonicalCurve l
    curve_eq := rfl
    a4_nonzero := canonicalCurve_a4_nonzero l
    a6_nonzero := canonicalCurve_a6_nonzero l
    c4_unit := canonicalCurve_c4_unit l
    delta_nonzero := canonicalCurve_delta_ne_zero l
    delta_norm := canonicalCurve_delta_norm_eq_q l
    elliptic := canonicalCurve_is_elliptic l }

theorem canonicalEllipticityPacket_curve :
    (canonicalEllipticityPacket l).curve = canonicalCurve l := rfl

theorem canonicalEllipticityPacket_a4_nonzero :
    (canonicalEllipticityPacket l).curve.a₄ ≠ 0 :=
  (canonicalEllipticityPacket l).a4_nonzero

theorem canonicalEllipticityPacket_a6_nonzero :
    (canonicalEllipticityPacket l).curve.a₆ ≠ 0 :=
  (canonicalEllipticityPacket l).a6_nonzero

theorem canonicalEllipticityPacket_c4_unit :
    IsUnit (canonicalEllipticityPacket l).curve.c₄ :=
  (canonicalEllipticityPacket l).c4_unit

theorem canonicalEllipticityPacket_delta_nonzero :
    (canonicalEllipticityPacket l).curve.Δ ≠ 0 :=
  (canonicalEllipticityPacket l).delta_nonzero

theorem canonicalEllipticityPacket_delta_norm :
    ‖(canonicalEllipticityPacket l).curve.Δ‖ = ‖q l‖ :=
  (canonicalEllipticityPacket l).delta_norm

theorem canonicalEllipticityPacket_elliptic :
    (canonicalEllipticityPacket l).curve.IsElliptic :=
  (canonicalEllipticityPacket l).elliptic

theorem canonicalEllipticityPacket_is_exact :
    (canonicalEllipticityPacket l).curve =
        TateCurve.weierstrassCurve ℚ_[l.value] (q l) := by
  rfl

theorem canonicalEllipticityPacket_source_delta :
    (canonicalEllipticityPacket l).curve.Δ =
        (TateCurve.a4 ℚ_[l.value] (q l)) ^ 2 -
          TateCurve.a6 ℚ_[l.value] (q l) -
          64 * (TateCurve.a4 ℚ_[l.value] (q l)) ^ 3 -
          432 * (TateCurve.a6 ℚ_[l.value] (q l)) ^ 2 +
          72 * TateCurve.a4 ℚ_[l.value] (q l) *
            TateCurve.a6 ℚ_[l.value] (q l) := by
  simpa [canonicalEllipticityPacket] using canonicalCurve_delta l

theorem canonicalEllipticityPacket_integral_presentation :
    ∃ W : WeierstrassCurve ℤ_[l.value],
      W.map (algebraMap (ℤ_[l.value]) (ℚ_[l.value])) =
        (canonicalEllipticityPacket l).curve := by
  rcases canonicalCurve_has_integral_presentation l with ⟨W, hW⟩
  exact ⟨W, by simpa [canonicalEllipticityPacket] using hW⟩

theorem canonicalEllipticityPacket_delta_is_nonunit_integral_witness :
    ∃ d : ℤ_[l.value], d ∈ nonunits ℤ_[l.value] ∧
      (d : ℚ_[l.value]) = (canonicalEllipticityPacket l).curve.Δ := by
  refine ⟨integralDelta l, integralDelta_mem_nonunits l, ?_⟩
  change (integralDelta l : ℚ_[l.value]) = (canonicalCurve l).Δ
  exact coe_integralDelta l

theorem canonicalEllipticityPacket_delta_residue_zero_witness :
    ∃ d : ℤ_[l.value],
      IsLocalRing.residue ℤ_[l.value] d = 0 ∧
        (d : ℚ_[l.value]) = (canonicalEllipticityPacket l).curve.Δ := by
  refine ⟨integralDelta l, ?_, ?_⟩
  · exact (by
      rw [IsLocalRing.residue_eq_zero_iff]
      exact integralDelta_mem_nonunits l)
  · change (integralDelta l : ℚ_[l.value]) = (canonicalCurve l).Δ
    exact coe_integralDelta l


theorem canonicalEllipticityPacket_complete_q_series_boundary :
    (canonicalEllipticityPacket l).curve.IsElliptic ∧
      (canonicalEllipticityPacket l).curve.Δ ≠ 0 ∧
      IsUnit (canonicalEllipticityPacket l).curve.c₄ ∧
      ‖(canonicalEllipticityPacket l).curve.Δ‖ = ‖q l‖ := by
  exact ⟨canonicalEllipticityPacket_elliptic l,
    canonicalEllipticityPacket_delta_nonzero l,
    canonicalEllipticityPacket_c4_unit l,
    canonicalEllipticityPacket_delta_norm l⟩

end ConsumerFacingOutput

section AuditPacket

structure DiscriminantAuditPacket (l : PrimeGeFive)
    [Fact (Nat.Prime l.value)] where
  qNorm : ℝ
  a6Norm : ℝ
  correctionNorm : ℝ
  qNorm_pos : 0 < qNorm
  qNorm_lt_one : qNorm < 1
  a6_norm_eq : a6Norm = qNorm
  correction_lt_a6 : correctionNorm < a6Norm
  deltaNorm : ℝ
  delta_norm_eq : deltaNorm = qNorm
  delta_nonzero : deltaValue l ≠ 0

def discriminantAuditPacket : DiscriminantAuditPacket l :=
  { qNorm := ‖q l‖
    a6Norm := ‖a6Value l‖
    correctionNorm := ‖deltaCorrection l‖
    deltaNorm := ‖deltaValue l‖
    qNorm_pos := q_norm_pos l
    qNorm_lt_one := q_norm_lt_one l
    a6_norm_eq := a6Value_norm l
    correction_lt_a6 := deltaCorrection_norm_lt_leading l
    delta_norm_eq := deltaValue_norm_eq_leading l
    delta_nonzero := by simpa [deltaValue] using canonicalCurve_delta_ne_zero l }

end AuditPacket

end TateCurvePadic

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def tateCurveDiscriminantEstimates : Obligation :=
  { id := "Foundations.Geometry.tate-curve-discriminant-estimates"
    source := "IUT I, Definition 3.1(c); canonical q-series discriminant"
    status := VerificationStatus.proved
    note :=
      "For q equal to the prime in Q_p with p >= 5, the expanded canonical " ++
        "discriminant is written as -a6 plus four correction terms. Each " ++
        "correction has strictly smaller p-adic norm than a6, so the " ++
        "discriminant is nonzero and has norm ||q||. An integral witness and " ++
        "its maximal-ideal membership are also constructed. This does not " ++
        "assert minimality, split reduction, or Tate uniformization."
    dependsOn := [ "Foundations.Geometry.tate-curve-padic-estimates" ] }

end LeanFormal.IUT.Audit
