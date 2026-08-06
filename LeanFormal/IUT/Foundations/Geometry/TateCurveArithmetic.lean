/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.Geometry.TateCurve
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Arithmetic closure of the canonical Tate equation

This file is the next source-facing prerequisite after the concrete local
Kummer/deck batch.  It records the exact arithmetic identities of the
canonical q-series Weierstrass equation and transports reduction certificates
through admissible changes of variables.

The file intentionally does **not** construct a Tate uniformization.  The
missing analytic theorem is represented only by the existing, explicit
`CurveIndexedTateUniformization` contract.  Every theorem below either is a
polynomial identity in the five Weierstrass coefficients or consumes a
written reduction certificate.  Thus a certificate cannot be mistaken for an
existence proof of the IUT input curve.

Source comparison: IUT I, Definition 3.1(b)-(c), and the arithmetic part of
the initial-theta discussion.  The q-series definitions follow the audited
`promachina/iut-lean` `SourceTateCurve.lean` source, but all names here belong
to the local project.
-/

namespace LeanFormal.IUT

universe u v

noncomputable section

namespace TateCurve

section Coefficients

variable {K : Type u} [NormedField K] [CharZero K]

/-! The five coefficients of the canonical equation are exposed first. -/

@[simp] theorem canonical_a₁ (q : K) :
    (weierstrassCurve K q).a₁ = 1 := by
  rfl

@[simp] theorem canonical_a₂ (q : K) :
    (weierstrassCurve K q).a₂ = 0 := by
  rfl

@[simp] theorem canonical_a₃ (q : K) :
    (weierstrassCurve K q).a₃ = 0 := by
  rfl

@[simp] theorem canonical_a₄ (q : K) :
    (weierstrassCurve K q).a₄ = a4 K q := by
  rfl

@[simp] theorem canonical_a₆ (q : K) :
    (weierstrassCurve K q).a₆ = a6 K q := by
  rfl

theorem canonical_equation_coefficients (q : K) :
    ((weierstrassCurve K q).a₁,
      (weierstrassCurve K q).a₂,
      (weierstrassCurve K q).a₃,
      (weierstrassCurve K q).a₄,
      (weierstrassCurve K q).a₆) =
      (1, 0, 0, a4 K q, a6 K q) := by
  rfl

theorem canonical_b₂ (q : K) :
    (weierstrassCurve K q).b₂ = 1 := by
  simp [WeierstrassCurve.b₂]

theorem canonical_b₄ (q : K) :
    (weierstrassCurve K q).b₄ = 2 * a4 K q := by
  simp [WeierstrassCurve.b₄]

theorem canonical_b₆ (q : K) :
    (weierstrassCurve K q).b₆ = 4 * a6 K q := by
  simp [WeierstrassCurve.b₆]

theorem canonical_b₈ (q : K) :
    (weierstrassCurve K q).b₈ = a6 K q - (a4 K q) ^ 2 := by
  simp [WeierstrassCurve.b₈]

theorem canonical_b_relation (q : K) :
    4 * (weierstrassCurve K q).b₈ =
      (weierstrassCurve K q).b₂ * (weierstrassCurve K q).b₆ -
        (weierstrassCurve K q).b₄ ^ 2 := by
  exact (weierstrassCurve K q).b_relation

theorem canonical_c₄ (q : K) :
    (weierstrassCurve K q).c₄ = 1 - 48 * a4 K q := by
  simp only [WeierstrassCurve.c₄, canonical_b₂, canonical_b₄]
  ring

theorem canonical_c₆ (q : K) :
    (weierstrassCurve K q).c₆ = -1 + 72 * a4 K q - 864 * a6 K q := by
  simp only [WeierstrassCurve.c₆, canonical_b₂, canonical_b₄, canonical_b₆]
  ring

theorem canonical_delta (q : K) :
    (weierstrassCurve K q).Δ =
      (a4 K q) ^ 2 - a6 K q - 64 * (a4 K q) ^ 3 -
        432 * (a6 K q) ^ 2 + 72 * a4 K q * a6 K q := by
  simp only [WeierstrassCurve.Δ, canonical_b₂, canonical_b₄, canonical_b₆,
    canonical_b₈]
  ring

theorem canonical_c_relation (q : K) :
    1728 * (weierstrassCurve K q).Δ =
      (weierstrassCurve K q).c₄ ^ 3 - (weierstrassCurve K q).c₆ ^ 2 := by
  exact (weierstrassCurve K q).c_relation

theorem canonical_delta_expanded_in_series (q : K) :
    (weierstrassCurve K q).Δ =
      (a4 K q) ^ 2 - a6 K q - 64 * (a4 K q) ^ 3 -
        432 * (a6 K q) ^ 2 + 72 * a4 K q * a6 K q :=
  canonical_delta q

theorem canonical_c₄_sub_one (q : K) :
    (weierstrassCurve K q).c₄ - 1 = -48 * a4 K q := by
  rw [canonical_c₄]
  ring

theorem canonical_c₆_add_one (q : K) :
    (weierstrassCurve K q).c₆ + 1 = 72 * a4 K q - 864 * a6 K q := by
  rw [canonical_c₆]
  ring

theorem canonical_delta_as_b₈_correction (q : K) :
    (weierstrassCurve K q).Δ =
      -(weierstrassCurve K q).b₈ -
        8 * (weierstrassCurve K q).b₄ ^ 3 -
        27 * (weierstrassCurve K q).b₆ ^ 2 +
        9 * (weierstrassCurve K q).b₄ * (weierstrassCurve K q).b₆ := by
  rw [WeierstrassCurve.Δ, canonical_b₂]
  ring

theorem canonical_delta_eq_zero_iff (q : K) :
    (weierstrassCurve K q).Δ = 0 ↔
      (a4 K q) ^ 2 - a6 K q - 64 * (a4 K q) ^ 3 -
        432 * (a6 K q) ^ 2 + 72 * a4 K q * a6 K q = 0 := by
  rw [canonical_delta]

theorem canonical_delta_ne_zero_iff (q : K) :
    (weierstrassCurve K q).Δ ≠ 0 ↔
      (a4 K q) ^ 2 - a6 K q - 64 * (a4 K q) ^ 3 -
        432 * (a6 K q) ^ 2 + 72 * a4 K q * a6 K q ≠ 0 := by
  rw [canonical_delta]

end Coefficients

section Contraction

variable {K : Type u} [NontriviallyNormedField K]

theorem q_ne_one_of_norm_lt_one {q : K} (hq : ‖q‖ < 1) : q ≠ 1 := by
  intro hq1
  rw [hq1] at hq
  norm_num at hq

theorem q_power_norm_lt_one {q : K} (hq : ‖q‖ < 1)
    (n : ℕ) (hn : 0 < n) : ‖q ^ n‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg q) hq hn.ne'

theorem q_power_ne_one {q : K} (hq : ‖q‖ < 1)
    (n : ℕ) (hn : 0 < n) : q ^ n ≠ 1 := by
  intro h
  have hnorm := q_power_norm_lt_one hq n hn
  rw [h] at hnorm
  norm_num at hnorm

theorem one_sub_q_power_ne_zero {q : K} (hq : ‖q‖ < 1)
    (n : ℕ) (hn : 0 < n) : 1 - q ^ n ≠ 0 := by
  exact sub_ne_zero.mpr (Ne.symm (q_power_ne_one hq n hn))

theorem q_power_ne_zero {q : K} (_hq : ‖q‖ < 1)
    (n : ℕ) (hq_ne_zero : q ≠ 0) : q ^ n ≠ 0 := by
  exact pow_ne_zero n hq_ne_zero

theorem denominator_unit {q : K} (hq : ‖q‖ < 1)
    (n : ℕ) (hn : 0 < n) : IsUnit (1 - q ^ n) := by
  exact isUnit_iff_ne_zero.mpr (one_sub_q_power_ne_zero hq n hn)

theorem denominator_inverse_ne_zero {q : K} (hq : ‖q‖ < 1)
    (n : ℕ) (hn : 0 < n) : (1 - q ^ n)⁻¹ ≠ 0 := by
  exact inv_ne_zero (one_sub_q_power_ne_zero hq n hn)

theorem lambert_term_zero (weight : ℕ) (q : K) :
    (0 : K) ^ weight * q ^ 0 / (1 - q ^ 0) = 0 := by
  simp

theorem lambertSeries_eq_sum_from_one
    (weight : ℕ) {q : K} (_hq : ‖q‖ < 1) :
    lambertSeries K weight q =
      ∑' n : ℕ, if 0 < n then
        (n : K) ^ weight * q ^ n / (1 - q ^ n) else 0 := by
  apply tsum_congr
  intro n
  by_cases hn : 0 < n
  · simp [hn]
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hn0
    simp

theorem lambertSeries_summable_from_one
    (weight : ℕ) {q : K} [CompleteSpace K]
    (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ if 0 < n then
      (n : K) ^ weight * q ^ n / (1 - q ^ n) else 0) := by
  convert TateCurve.lambertSeries_summable K weight hq using 1
  funext n
  by_cases hn : 0 < n
  · simp [hn]
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hn0
    simp

theorem lambertSeries_norm_le
    (weight : ℕ) {q : K} [CompleteSpace K]
    (_hq : ‖q‖ < 1)
    (hnorm : Summable (fun n : ℕ ↦
      ‖(n : K) ^ weight * q ^ n / (1 - q ^ n)‖)) :
    ‖lambertSeries K weight q‖ ≤
      ∑' n : ℕ, ‖(n : K) ^ weight * q ^ n / (1 - q ^ n)‖ := by
  exact norm_tsum_le_tsum_norm hnorm

theorem lambertSeries_zero (weight : ℕ) :
    lambertSeries K weight 0 = 0 := by
  change (∑' n : ℕ, (n : K) ^ weight * 0 ^ n / (1 - 0 ^ n)) = 0
  have hzero :
      (fun n : ℕ ↦ (n : K) ^ weight * 0 ^ n / (1 - 0 ^ n)) =
        (fun _ : ℕ ↦ (0 : K)) := by
    funext n
    cases n with
    | zero => simp
    | succ n => simp
  rw [hzero]
  simp

theorem a4_zero [CharZero K] : a4 K 0 = 0 := by
  simp [a4, lambertSeries_zero]

theorem a6_zero [CharZero K] : a6 K 0 = 0 := by
  simp [a6, lambertSeries_zero]

end Contraction

section Ellipticity

variable {K : Type u} [NontriviallyNormedField K] [CharZero K]

/-- The exact nondegeneracy certificate for the canonical q-series equation. -/
structure ArithmeticCertificate (q : K) where
  q_ne_zero : q ≠ 0
  q_norm_lt_one : ‖q‖ < 1
  delta_ne_zero : (weierstrassCurve K q).Δ ≠ 0

namespace ArithmeticCertificate

variable {q : K} (certificate : ArithmeticCertificate q)
include certificate

theorem q_ne_one : q ≠ 1 := by
  exact q_ne_one_of_norm_lt_one (ArithmeticCertificate.q_norm_lt_one certificate)

theorem q_power_ne_zero (n : ℕ) : q ^ n ≠ 0 := by
  exact pow_ne_zero n (ArithmeticCertificate.q_ne_zero certificate)

theorem q_power_norm_lt_one (n : ℕ) (hn : 0 < n) : ‖q ^ n‖ < 1 := by
  exact TateCurve.q_power_norm_lt_one
    (ArithmeticCertificate.q_norm_lt_one certificate) n hn

theorem denominator_unit (n : ℕ) (hn : 0 < n) :
    IsUnit (1 - q ^ n) := by
  exact TateCurve.denominator_unit
    (ArithmeticCertificate.q_norm_lt_one certificate) n hn

theorem canonical_delta_unit :
    IsUnit (weierstrassCurve K q).Δ := by
  exact isUnit_iff_ne_zero.mpr (ArithmeticCertificate.delta_ne_zero certificate)

theorem canonical_is_elliptic :
    (weierstrassCurve K q).IsElliptic := by
  exact ⟨ArithmeticCertificate.canonical_delta_unit certificate⟩

omit certificate in
theorem canonical_is_elliptic_iff :
    (weierstrassCurve K q).IsElliptic ↔
      IsUnit (weierstrassCurve K q).Δ := by
  exact WeierstrassCurve.isElliptic_iff (weierstrassCurve K q)

theorem canonical_j_defined :
    letI : (weierstrassCurve K q).IsElliptic :=
      ArithmeticCertificate.canonical_is_elliptic certificate
    (weierstrassCurve K q).j =
      (weierstrassCurve K q).Δ'⁻¹ * (weierstrassCurve K q).c₄ ^ 3 := by
  rfl

omit certificate in
theorem canonical_c_relation :
    1728 * (weierstrassCurve K q).Δ =
      (weierstrassCurve K q).c₄ ^ 3 - (weierstrassCurve K q).c₆ ^ 2 := by
  exact (weierstrassCurve K q).c_relation

omit certificate in
theorem canonical_delta_expansion :
    (weierstrassCurve K q).Δ =
      (a4 K q) ^ 2 - a6 K q - 64 * (a4 K q) ^ 3 -
        432 * (a6 K q) ^ 2 + 72 * a4 K q * a6 K q := by
  exact canonical_delta q

omit certificate in
theorem canonical_c₄_expansion :
    (weierstrassCurve K q).c₄ = 1 - 48 * a4 K q := by
  exact canonical_c₄ q

omit certificate in
theorem canonical_c₆_expansion :
    (weierstrassCurve K q).c₆ = -1 + 72 * a4 K q - 864 * a6 K q := by
  exact canonical_c₆ q

omit certificate in
theorem canonical_delta_nonzero_of_expansion
    (hexp : (a4 K q) ^ 2 - a6 K q - 64 * (a4 K q) ^ 3 -
      432 * (a6 K q) ^ 2 + 72 * a4 K q * a6 K q ≠ 0) :
    (weierstrassCurve K q).Δ ≠ 0 := by
  rw [canonical_delta]
  exact hexp

end ArithmeticCertificate

theorem canonical_is_elliptic_of_delta_ne_zero {q : K}
    (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (hΔ : (weierstrassCurve K q).Δ ≠ 0) :
    (weierstrassCurve K q).IsElliptic := by
  exact ArithmeticCertificate.canonical_is_elliptic
    (ArithmeticCertificate.mk hq0 hq hΔ)

theorem canonical_delta_unit_iff {q : K} :
    IsUnit (weierstrassCurve K q).Δ ↔
      (weierstrassCurve K q).Δ ≠ 0 :=
  isUnit_iff_ne_zero

theorem canonical_is_elliptic_iff_delta_ne_zero {q : K} :
    (weierstrassCurve K q).IsElliptic ↔
      (weierstrassCurve K q).Δ ≠ 0 := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]

end Ellipticity

section VariableChange

variable {K : Type u} [NormedField K] [CharZero K]

theorem delta_variableChange (q : K)
    (C : WeierstrassCurve.VariableChange K) :
    (C • weierstrassCurve K q).Δ =
      C.u⁻¹ ^ 12 * (weierstrassCurve K q).Δ := by
  exact WeierstrassCurve.variableChange_Δ (weierstrassCurve K q) C

theorem c₄_variableChange (q : K)
    (C : WeierstrassCurve.VariableChange K) :
    (C • weierstrassCurve K q).c₄ =
      C.u⁻¹ ^ 4 * (weierstrassCurve K q).c₄ := by
  exact WeierstrassCurve.variableChange_c₄ (weierstrassCurve K q) C

theorem delta_variableChange_ne_zero_iff (q : K)
    (C : WeierstrassCurve.VariableChange K) :
    (C • weierstrassCurve K q).Δ ≠ 0 ↔
      (weierstrassCurve K q).Δ ≠ 0 := by
  rw [delta_variableChange]
  constructor
  · intro h hΔ
    exact h (by rw [hΔ, mul_zero])
  · intro h hΔ
    apply h
    exact (mul_eq_zero.mp hΔ).resolve_left (by simp)

theorem c₄_variableChange_eq_zero_iff (q : K)
    (C : WeierstrassCurve.VariableChange K) :
    (C • weierstrassCurve K q).c₄ = 0 ↔
      (weierstrassCurve K q).c₄ = 0 := by
  rw [c₄_variableChange]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (by simp)
  · intro h
    rw [h, mul_zero]

omit [CharZero K] in
theorem variableChange_preserves_ellipticity
    {W : WeierstrassCurve K} (hW : W.IsElliptic)
    (C : WeierstrassCurve.VariableChange K) :
    (C • W).IsElliptic := by
  have hunit : IsUnit W.Δ := hW.isUnit
  refine ⟨?_⟩
  rw [WeierstrassCurve.variableChange_Δ]
  exact (C.u⁻¹.isUnit.pow 12).mul hunit

omit [CharZero K] in
theorem variableChange_preserves_delta_nonzero
    {W : WeierstrassCurve K} (hW : W.Δ ≠ 0)
    (C : WeierstrassCurve.VariableChange K) :
    (C • W).Δ ≠ 0 := by
  rw [WeierstrassCurve.variableChange_Δ]
  exact mul_ne_zero (by simp) hW

omit [CharZero K] in
theorem inverse_variableChange_preserves_delta_nonzero
    {W : WeierstrassCurve K} (hW : W.Δ ≠ 0)
    (C : WeierstrassCurve.VariableChange K) :
    (C⁻¹ • W).Δ ≠ 0 := by
  exact variableChange_preserves_delta_nonzero hW C⁻¹

theorem variableChange_delta_ratio (q : K)
    (hΔ : (weierstrassCurve K q).Δ ≠ 0)
    (C : WeierstrassCurve.VariableChange K) :
  (C • weierstrassCurve K q).Δ /
        (weierstrassCurve K q).Δ = C.u⁻¹ ^ 12 := by
  rw [delta_variableChange]
  field_simp [hΔ]

theorem variableChange_c₄_ratio (q : K)
    (h₄ : (weierstrassCurve K q).c₄ ≠ 0)
    (C : WeierstrassCurve.VariableChange K) :
    (C • weierstrassCurve K q).c₄ /
        (weierstrassCurve K q).c₄ = C.u⁻¹ ^ 4 := by
  rw [c₄_variableChange]
  field_simp [h₄]

omit [CharZero K] in
theorem variableChange_j_invariant
    {W : WeierstrassCurve K} (hW : W.IsElliptic)
    (C : WeierstrassCurve.VariableChange K) :
    letI : W.IsElliptic := hW
    letI : (C • W).IsElliptic := variableChange_preserves_ellipticity hW C
    (C • W).j = W.j := by
  exact WeierstrassCurve.variableChange_j W C

end VariableChange

section ReductionCertificates

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

def HasStableReductionOnMinimalModel (W : WeierstrassCurve K) : Prop :=
  HasGoodReductionOnMinimalModel R W ∨
    HasMultiplicativeReductionOnMinimalModel R W

/-!
The following records are certificates, not constructors.  They keep the
minimal-model witness and valuation equalities next to the curve they refer
to, so later source-facing code cannot accidentally use a fact for a
different coordinate presentation.
-/

structure MultiplicativeCertificate (W : WeierstrassCurve K) where
  coordinateChange : WeierstrassCurve.VariableChange K
  integral : WeierstrassCurve.IsIntegral R (coordinateChange • W)
  minimal : WeierstrassCurve.IsMinimal R (coordinateChange • W)
  delta_lt_one :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K
      (coordinateChange • W).Δ < 1
  c₄_eq_one :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K
      (coordinateChange • W).c₄ = 1

namespace MultiplicativeCertificate

variable {W : WeierstrassCurve K}

noncomputable def transformed (certificate : MultiplicativeCertificate R W) :
    WeierstrassCurve K :=
  certificate.coordinateChange • W

theorem hasMultiplicativeReduction
    (certificate : MultiplicativeCertificate R W) :
    (certificate.coordinateChange • W).HasMultiplicativeReduction R := by
  exact
    { toIsMinimal := certificate.minimal
      badReduction := certificate.delta_lt_one
      multiplicativeReduction := certificate.c₄_eq_one }

theorem hasMultiplicativeReductionOnMinimalModel
    (certificate : MultiplicativeCertificate R W) :
    HasMultiplicativeReductionOnMinimalModel R W := by
  exact ⟨certificate.coordinateChange, certificate.hasMultiplicativeReduction⟩

theorem coordinateChange_isIntegral
    (certificate : MultiplicativeCertificate R W) :
    WeierstrassCurve.IsIntegral R certificate.transformed :=
  certificate.integral

theorem coordinateChange_isMinimal
    (certificate : MultiplicativeCertificate R W) :
    WeierstrassCurve.IsMinimal R certificate.transformed :=
  certificate.minimal

theorem discriminant_valuation_lt_one
    (certificate : MultiplicativeCertificate R W) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K
      certificate.transformed.Δ < 1 :=
  certificate.delta_lt_one

theorem c₄_valuation_eq_one
    (certificate : MultiplicativeCertificate R W) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K
      certificate.transformed.c₄ = 1 :=
  certificate.c₄_eq_one

theorem stable_reduction
    (certificate : MultiplicativeCertificate R W) :
    HasMultiplicativeReductionOnMinimalModel R W :=
  certificate.hasMultiplicativeReductionOnMinimalModel

end MultiplicativeCertificate

structure GoodCertificate (W : WeierstrassCurve K) where
  coordinateChange : WeierstrassCurve.VariableChange K
  integral : WeierstrassCurve.IsIntegral R (coordinateChange • W)
  minimal : WeierstrassCurve.IsMinimal R (coordinateChange • W)
  delta_eq_one :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K
      (coordinateChange • W).Δ = 1

namespace GoodCertificate

variable {W : WeierstrassCurve K}

noncomputable def transformed (certificate : GoodCertificate R W) :
    WeierstrassCurve K :=
  certificate.coordinateChange • W

theorem hasGoodReduction
    (certificate : GoodCertificate R W) :
    certificate.transformed.HasGoodReduction R := by
  exact
    { toIsMinimal := certificate.minimal
      goodReduction := certificate.delta_eq_one }

theorem hasGoodReductionOnMinimalModel
    (certificate : GoodCertificate R W) :
    HasGoodReductionOnMinimalModel R W := by
  exact ⟨certificate.coordinateChange, certificate.hasGoodReduction⟩

theorem coordinateChange_isIntegral
    (certificate : GoodCertificate R W) :
    WeierstrassCurve.IsIntegral R certificate.transformed :=
  certificate.integral

theorem coordinateChange_isMinimal
    (certificate : GoodCertificate R W) :
    WeierstrassCurve.IsMinimal R certificate.transformed :=
  certificate.minimal

theorem discriminant_valuation_eq_one
    (certificate : GoodCertificate R W) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation K
      certificate.transformed.Δ = 1 :=
  certificate.delta_eq_one

theorem stable_reduction
    (certificate : GoodCertificate R W) :
    HasGoodReductionOnMinimalModel R W :=
  certificate.hasGoodReductionOnMinimalModel

end GoodCertificate

theorem good_or_multiplicative_of_minimal
    {W : WeierstrassCurve K} (hW : WeierstrassCurve.IsMinimal R W) :
    W.HasGoodReduction R ∨ W.HasMultiplicativeReduction R ∨
      W.HasAdditiveReduction R := by
  letI : WeierstrassCurve.IsMinimal R W := hW
  exact WeierstrassCurve.hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R

theorem good_certificate_stable
    {W : WeierstrassCurve K} (certificate : GoodCertificate R W) :
    HasStableReductionOnMinimalModel R W := by
  exact Or.inl certificate.hasGoodReductionOnMinimalModel

theorem multiplicative_certificate_stable
    {W : WeierstrassCurve K} (certificate : MultiplicativeCertificate R W) :
    HasStableReductionOnMinimalModel R W := by
  exact Or.inr certificate.hasMultiplicativeReductionOnMinimalModel

end ReductionCertificates

section ReductionTransport

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

theorem hasGoodReductionOnMinimalModel_of_equation_eq
    {W W' : WeierstrassCurve K} (h : W = W')
    (hW : HasGoodReductionOnMinimalModel R W) :
    HasGoodReductionOnMinimalModel R W' := by
  simpa [h] using hW

theorem hasMultiplicativeReductionOnMinimalModel_of_equation_eq
    {W W' : WeierstrassCurve K} (h : W = W')
    (hW : HasMultiplicativeReductionOnMinimalModel R W) :
    HasMultiplicativeReductionOnMinimalModel R W' := by
  simpa [h] using hW

theorem hasStableReductionOnMinimalModel_of_equation_eq
    {W W' : WeierstrassCurve K} (h : W = W')
    (hW : HasStableReductionOnMinimalModel R W) :
    HasStableReductionOnMinimalModel R W' := by
  simpa [h] using hW

theorem hasGoodReductionOnMinimalModel_smul_transport
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) :
    HasGoodReductionOnMinimalModel R (C • W) ↔
      HasGoodReductionOnMinimalModel R W := by
  exact hasGoodReductionOnMinimalModel_smul_iff R C W

theorem hasMultiplicativeReductionOnMinimalModel_smul_transport
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) :
    HasMultiplicativeReductionOnMinimalModel R (C • W) ↔
      HasMultiplicativeReductionOnMinimalModel R W := by
  exact hasMultiplicativeReductionOnMinimalModel_smul_iff R C W

theorem hasSplitMultiplicativeReductionOnMinimalModel_smul_transport
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) :
    HasSplitMultiplicativeReductionOnMinimalModel R (C • W) ↔
      HasSplitMultiplicativeReductionOnMinimalModel R W := by
  exact hasSplitMultiplicativeReductionOnMinimalModel_smul_iff R C W

theorem hasStableReductionOnMinimalModel_smul_transport
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) :
    HasStableReductionOnMinimalModel R (C • W) ↔
      HasStableReductionOnMinimalModel R W := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl ((hasGoodReductionOnMinimalModel_smul_transport C W).mp h)
    · exact Or.inr ((hasMultiplicativeReductionOnMinimalModel_smul_transport C W).mp h)
  · intro h
    rcases h with h | h
    · exact Or.inl ((hasGoodReductionOnMinimalModel_smul_transport C W).mpr h)
    · exact Or.inr ((hasMultiplicativeReductionOnMinimalModel_smul_transport C W).mpr h)

end ReductionTransport

section TateReduction

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type v} [NormedField K] [CharZero K]
  [Algebra R K] [IsFractionRing R K]
variable {q : K}

theorem canonical_multiplicative_certificate_is_source_predicate
    (certificate : MultiplicativeCertificate R (TateCurve.weierstrassCurve K q)) :
    HasMultiplicativeReductionOnMinimalModel R
      (TateCurve.weierstrassCurve K q) := by
  exact certificate.hasMultiplicativeReductionOnMinimalModel

theorem canonical_good_certificate_is_source_predicate
    (certificate : GoodCertificate R (TateCurve.weierstrassCurve K q)) :
    HasGoodReductionOnMinimalModel R
      (TateCurve.weierstrassCurve K q) := by
  exact certificate.hasGoodReductionOnMinimalModel

theorem canonical_multiplicative_certificate_stable
    (certificate : MultiplicativeCertificate R (TateCurve.weierstrassCurve K q)) :
    HasStableReductionOnMinimalModel R
      (TateCurve.weierstrassCurve K q) := by
  exact multiplicative_certificate_stable (R := R) certificate

theorem canonical_good_certificate_stable
    (certificate : GoodCertificate R (TateCurve.weierstrassCurve K q)) :
    HasStableReductionOnMinimalModel R
      (TateCurve.weierstrassCurve K q) := by
  exact good_certificate_stable (R := R) certificate

theorem canonical_certificate_delta_nonzero_of_transformed
    (certificate : MultiplicativeCertificate R (TateCurve.weierstrassCurve K q))
    (htrans :
      (certificate.coordinateChange •
        TateCurve.weierstrassCurve K q).Δ ≠ 0) :
    (TateCurve.weierstrassCurve K q).Δ ≠ 0 := by
  intro hzero
  apply htrans
  rw [WeierstrassCurve.variableChange_Δ, hzero, mul_zero]

theorem canonical_certificate_c₄_nonzero_of_transformed
    (certificate : MultiplicativeCertificate R (TateCurve.weierstrassCurve K q))
    (htrans :
      (certificate.coordinateChange •
        TateCurve.weierstrassCurve K q).c₄ ≠ 0) :
    (TateCurve.weierstrassCurve K q).c₄ ≠ 0 := by
  intro hzero
  apply htrans
  rw [WeierstrassCurve.variableChange_c₄, hzero, mul_zero]

end TateReduction

section CurveIndexedTransport

variable {F : Type u} [Field F] [NumberField F]
variable {place : NumberField.FinitePlace F}
variable {X : PuncturedEllipticCurve F}
variable {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}

namespace CurveIndexedTateUniformization

variable (realization : CurveIndexedTateUniformization X place parameter)
include realization

theorem local_curve_equation :
    realization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q =
      (X.baseChange (NumberFieldFinitePlace.Completion place)).curve :=
  realization.realizesCurve

theorem canonical_curve_elliptic :
    (TateCurve.weierstrassCurve
      (NumberFieldFinitePlace.Completion place) parameter.q).IsElliptic :=
  realization.canonicalIsElliptic

omit realization in
theorem local_curve_elliptic :
    ((X.baseChange (NumberFieldFinitePlace.Completion place)).curve).IsElliptic :=
  (X.baseChange (NumberFieldFinitePlace.Completion place)).isElliptic

theorem local_curve_delta_eq_transformed :
    ((X.baseChange (NumberFieldFinitePlace.Completion place)).curve).Δ =
      (realization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q).Δ := by
  rw [local_curve_equation realization]

theorem local_curve_c₄_eq_transformed :
    ((X.baseChange (NumberFieldFinitePlace.Completion place)).curve).c₄ =
      (realization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q).c₄ := by
  rw [local_curve_equation realization]

theorem local_curve_c₆_eq_transformed :
    ((X.baseChange (NumberFieldFinitePlace.Completion place)).curve).c₆ =
      (realization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q).c₆ := by
  rw [local_curve_equation realization]

theorem local_curve_b₂_eq_transformed :
    ((X.baseChange (NumberFieldFinitePlace.Completion place)).curve).b₂ =
      (realization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q).b₂ := by
  rw [local_curve_equation realization]

theorem local_curve_b₄_eq_transformed :
    ((X.baseChange (NumberFieldFinitePlace.Completion place)).curve).b₄ =
      (realization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q).b₄ := by
  rw [local_curve_equation realization]

theorem local_curve_b₆_eq_transformed :
    ((X.baseChange (NumberFieldFinitePlace.Completion place)).curve).b₆ =
      (realization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q).b₆ := by
  rw [local_curve_equation realization]

theorem canonical_delta_ne_zero :
    (TateCurve.weierstrassCurve
      (NumberFieldFinitePlace.Completion place) parameter.q).Δ ≠ 0 := by
  exact (canonical_curve_elliptic realization).isUnit.ne_zero

theorem transformed_delta_ne_zero :
    (realization.coordinateChange •
      TateCurve.weierstrassCurve
        (NumberFieldFinitePlace.Completion place) parameter.q).Δ ≠ 0 := by
  rw [WeierstrassCurve.variableChange_Δ]
  exact mul_ne_zero (by simp) (canonical_delta_ne_zero realization)

theorem local_curve_delta_ne_zero :
    ((X.baseChange (NumberFieldFinitePlace.Completion place)).curve).Δ ≠ 0 := by
  rw [local_curve_delta_eq_transformed realization]
  exact transformed_delta_ne_zero realization

theorem local_curve_is_elliptic_of_transport :
    ((X.baseChange (NumberFieldFinitePlace.Completion place)).curve).IsElliptic := by
  exact ⟨isUnit_iff_ne_zero.mpr (local_curve_delta_ne_zero realization)⟩

theorem good_reduction_transport
    {R : Type v} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R (NumberFieldFinitePlace.Completion place)]
    [IsFractionRing R (NumberFieldFinitePlace.Completion place)]
    (h : HasGoodReductionOnMinimalModel R
      (realization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q)) :
    HasGoodReductionOnMinimalModel R
      ((X.baseChange (NumberFieldFinitePlace.Completion place)).curve) := by
  exact hasGoodReductionOnMinimalModel_of_equation_eq
    (local_curve_equation realization) h

theorem multiplicative_reduction_transport
    {R : Type v} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R (NumberFieldFinitePlace.Completion place)]
    [IsFractionRing R (NumberFieldFinitePlace.Completion place)]
    (h : HasMultiplicativeReductionOnMinimalModel R
      (realization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q)) :
    HasMultiplicativeReductionOnMinimalModel R
      ((X.baseChange (NumberFieldFinitePlace.Completion place)).curve) := by
  exact hasMultiplicativeReductionOnMinimalModel_of_equation_eq
    (local_curve_equation realization) h

theorem stable_reduction_transport
    {R : Type v} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R (NumberFieldFinitePlace.Completion place)]
    [IsFractionRing R (NumberFieldFinitePlace.Completion place)]
    (h : HasStableReductionOnMinimalModel R
      (realization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q)) :
    HasStableReductionOnMinimalModel R
      ((X.baseChange (NumberFieldFinitePlace.Completion place)).curve) := by
  exact hasStableReductionOnMinimalModel_of_equation_eq
    (local_curve_equation realization) h

theorem reduction_transport_back
    {R : Type v} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R (NumberFieldFinitePlace.Completion place)]
    [IsFractionRing R (NumberFieldFinitePlace.Completion place)]
    (h : HasStableReductionOnMinimalModel R
      ((X.baseChange (NumberFieldFinitePlace.Completion place)).curve)) :
    HasStableReductionOnMinimalModel R
      (realization.coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q) := by
  exact hasStableReductionOnMinimalModel_of_equation_eq
    (local_curve_equation realization).symm h

end CurveIndexedTateUniformization

end CurveIndexedTransport

section CertificateAssembly

variable {K : Type u} [NontriviallyNormedField K] [CharZero K]

/-! Small constructors keep the certificate boundary explicit. -/

theorem ArithmeticCertificate.of_delta_ne_zero
    {q : K} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hΔ : (TateCurve.weierstrassCurve K q).Δ ≠ 0) :
    TateCurve.ArithmeticCertificate q :=
  { q_ne_zero := hq0
    q_norm_lt_one := hq
    delta_ne_zero := hΔ }

theorem ArithmeticCertificate.canonical_curve_has_unit_delta
    {q : K} (certificate : TateCurve.ArithmeticCertificate q) :
    IsUnit (TateCurve.weierstrassCurve K q).Δ :=
  TateCurve.ArithmeticCertificate.canonical_delta_unit certificate

theorem ArithmeticCertificate.canonical_curve_delta_ne_zero
    {q : K} (certificate : TateCurve.ArithmeticCertificate q) :
    (TateCurve.weierstrassCurve K q).Δ ≠ 0 :=
  TateCurve.ArithmeticCertificate.delta_ne_zero certificate

theorem ArithmeticCertificate.canonical_curve_q_nonzero
    {q : K} (certificate : TateCurve.ArithmeticCertificate q) : q ≠ 0 :=
  TateCurve.ArithmeticCertificate.q_ne_zero certificate

theorem ArithmeticCertificate.canonical_curve_q_contracts
    {q : K} (certificate : TateCurve.ArithmeticCertificate q) : ‖q‖ < 1 :=
  TateCurve.ArithmeticCertificate.q_norm_lt_one certificate

namespace ArithmeticCertificate

variable {q : K} (certificate : TateCurve.ArithmeticCertificate q)
include certificate

theorem lambertSeries_summable (weight : ℕ) [CompleteSpace K] :
    Summable (fun n : ℕ ↦
      (n : K) ^ weight * q ^ n / (1 - q ^ n)) := by
  exact TateCurve.lambertSeries_summable K weight
    (TateCurve.ArithmeticCertificate.q_norm_lt_one certificate)

theorem positive_power_contraction (n : ℕ) (hn : 0 < n) :
    ‖q ^ n‖ < 1 := by
  exact TateCurve.ArithmeticCertificate.q_power_norm_lt_one certificate n hn

theorem positive_power_denominator_unit (n : ℕ) (hn : 0 < n) :
    IsUnit (1 - q ^ n) := by
  exact TateCurve.ArithmeticCertificate.denominator_unit certificate n hn

theorem positive_power_denominator_ne_zero (n : ℕ) (hn : 0 < n) :
    1 - q ^ n ≠ 0 := by
  exact isUnit_iff_ne_zero.mp
    (TateCurve.ArithmeticCertificate.denominator_unit certificate n hn)

omit certificate in
theorem canonical_curve_b₂ :
    (TateCurve.weierstrassCurve K q).b₂ = 1 := by
  exact TateCurve.canonical_b₂ q

omit certificate in
theorem canonical_curve_b₄ :
    (TateCurve.weierstrassCurve K q).b₄ = 2 * TateCurve.a4 K q := by
  exact TateCurve.canonical_b₄ q

omit certificate in
theorem canonical_curve_b₆ :
    (TateCurve.weierstrassCurve K q).b₆ = 4 * TateCurve.a6 K q := by
  exact TateCurve.canonical_b₆ q

omit certificate in
theorem canonical_curve_b₈ :
    (TateCurve.weierstrassCurve K q).b₈ =
      TateCurve.a6 K q - (TateCurve.a4 K q) ^ 2 := by
  exact TateCurve.canonical_b₈ q

omit certificate in
theorem canonical_curve_c₄ :
    (TateCurve.weierstrassCurve K q).c₄ =
      1 - 48 * TateCurve.a4 K q := by
  exact TateCurve.canonical_c₄ q

omit certificate in
theorem canonical_curve_c₆ :
    (TateCurve.weierstrassCurve K q).c₆ =
      -1 + 72 * TateCurve.a4 K q - 864 * TateCurve.a6 K q := by
  exact TateCurve.canonical_c₆ q

omit certificate in
theorem canonical_curve_delta :
    (TateCurve.weierstrassCurve K q).Δ =
      (TateCurve.a4 K q) ^ 2 - TateCurve.a6 K q -
        64 * (TateCurve.a4 K q) ^ 3 -
        432 * (TateCurve.a6 K q) ^ 2 +
        72 * TateCurve.a4 K q * TateCurve.a6 K q := by
  exact TateCurve.canonical_delta q

theorem canonical_curve_j_formula :
    letI : (TateCurve.weierstrassCurve K q).IsElliptic :=
      TateCurve.ArithmeticCertificate.canonical_is_elliptic certificate
    (TateCurve.weierstrassCurve K q).j =
      (TateCurve.weierstrassCurve K q).Δ'⁻¹ *
        (TateCurve.weierstrassCurve K q).c₄ ^ 3 := by
  rfl

theorem canonical_curve_delta_unit :
    IsUnit (TateCurve.weierstrassCurve K q).Δ :=
  TateCurve.ArithmeticCertificate.canonical_delta_unit certificate

theorem canonical_curve_is_elliptic :
    (TateCurve.weierstrassCurve K q).IsElliptic :=
  TateCurve.ArithmeticCertificate.canonical_is_elliptic certificate

end ArithmeticCertificate

end CertificateAssembly

end TateCurve

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def tateCurveArithmeticClosure : Obligation :=
  { id := "Foundations.Geometry.tate-curve-arithmetic-closure"
    source := "IUT I, Definition 3.1(b)-(c); Weierstrass/Tate arithmetic"
    status := VerificationStatus.proved
    note :=
      "The canonical q-series equation's b₂, b₄, b₆, b₈, c₄, c₆, and " ++
        "discriminant formulas are proved by coefficient reduction. " ++
        "Variable-change weights, ellipticity from a nonzero discriminant, " ++
        "and certificate-based good/multiplicative/stable reduction transport " ++
        "are also proved. The file does not prove the discriminant is nonzero " ++
        "for q=p, nor does it construct Tate uniformization or an etale object."
    dependsOn :=
      [ "Foundations.Geometry.tate-curve-q-series",
        "Foundations.Geometry.elliptic-local-reduction",
        "Foundations.Geometry.curve-indexed-tate-uniformization" ] }

end LeanFormal.IUT.Audit
