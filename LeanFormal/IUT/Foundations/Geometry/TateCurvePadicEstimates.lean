/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# p-adic estimates for the canonical Tate Lambert series

This module is the next concrete prerequisite for the C layer.  It fixes the
local parameter to the actual element `q = p` in `Q_p`, and proves the
ultrametric estimates needed before a discriminant computation can be trusted.
The proof is deliberately split into the series term, the tail, and the two
canonical coefficients.  No Tate uniformization, comparison with an input
elliptic curve, or nonzero-discriminant theorem is smuggled into a certificate.

The main output is the strict first-term estimate

`||tail|| < ||q/(1-q)||`.

This is an honest p-adic statement: it uses `p >= 5`, the exact norm of the
prime in `Q_p`, and the nonarchimedean equality for unequal norms.  It is
strong enough to prove that `a4`, `a6`, and `c4` are nonzero for the canonical
q-series equation.  It is not, by itself, a proof that the discriminant is
nonzero; that remaining obligation is recorded at the end of the file.
-/

namespace LeanFormal.IUT

noncomputable section

namespace TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

section BasicParameter

def q : ℚ_[l.value] := (l.value : ℚ_[l.value])

@[simp] theorem q_eq_prime : q l = (l.value : ℚ_[l.value]) := rfl

theorem q_ne_zero : q l ≠ 0 := by
  exact Nat.cast_ne_zero.mpr l.prime.ne_zero

theorem q_norm_eq : ‖q l‖ = (l.value : ℝ)⁻¹ := by
  simp [q, Padic.norm_p]

theorem q_norm_lt_one : ‖q l‖ < 1 := by
  simpa [q] using (Padic.norm_p_lt_one (p := l.value))

theorem q_norm_pos : 0 < ‖q l‖ :=
  norm_pos_iff.mpr (q_ne_zero l)

theorem q_norm_nonneg : 0 ≤ ‖q l‖ :=
  (q_norm_pos l).le

theorem q_norm_lt_half : ‖q l‖ < (1 : ℝ) / 2 := by
  rw [q_norm_eq l]
  have hpos : 0 < (l.value : ℝ) := by
    exact_mod_cast l.prime.pos
  have hfive : (5 : ℝ) ≤ (l.value : ℝ) := by
    exact_mod_cast l.ge_five
  have hinv : (l.value : ℝ)⁻¹ ≤ (5 : ℝ)⁻¹ :=
    (inv_le_inv₀ hpos (by norm_num)).2 hfive
  calc
    (l.value : ℝ)⁻¹ ≤ (5 : ℝ)⁻¹ := hinv
    _ < (1 : ℝ) / 2 := by norm_num

theorem q_power_ne_zero (n : ℕ) : q l ^ n ≠ 0 := by
  exact pow_ne_zero n (q_ne_zero l)

theorem q_power_norm_eq (n : ℕ) : ‖q l ^ n‖ = ‖q l‖ ^ n := by
  exact norm_pow _ _

theorem q_power_norm_lt_one {n : ℕ} (hn : 0 < n) : ‖q l ^ n‖ < 1 := by
  exact TateCurve.q_power_norm_lt_one (q_norm_lt_one l) n hn

theorem q_power_norm_nonneg (n : ℕ) : 0 ≤ ‖q l ^ n‖ :=
  norm_nonneg _

theorem q_power_ne_one {n : ℕ} (hn : 0 < n) : q l ^ n ≠ 1 := by
  exact TateCurve.q_power_ne_one (q_norm_lt_one l) n hn

theorem denominator_ne_zero {n : ℕ} (hn : 0 < n) : 1 - q l ^ n ≠ 0 := by
  exact TateCurve.one_sub_q_power_ne_zero (q_norm_lt_one l) n hn

theorem denominator_is_unit {n : ℕ} (hn : 0 < n) :
    IsUnit (1 - q l ^ n) := by
  exact TateCurve.denominator_unit (q_norm_lt_one l) n hn

theorem denominator_inverse_ne_zero {n : ℕ} (hn : 0 < n) :
    (1 - q l ^ n)⁻¹ ≠ 0 := by
  exact inv_ne_zero (denominator_ne_zero l hn)

theorem denominator_norm_eq_one {n : ℕ} (hn : 0 < n) :
    ‖1 - q l ^ n‖ = 1 := by
  have hpow := q_power_norm_lt_one l hn
  have hneq : ‖(1 : ℚ_[l.value])‖ ≠ ‖-(q l ^ n)‖ := by
    simp only [norm_one, norm_neg]
    exact ne_of_gt hpow
  rw [show (1 : ℚ_[l.value]) - q l ^ n = 1 + -(q l ^ n) by ring]
  rw [Padic.add_eq_max_of_ne hneq]
  simp only [norm_one, norm_neg, max_eq_left (le_of_lt hpow)]

theorem denominator_inverse_norm_eq_one {n : ℕ} (hn : 0 < n) :
    ‖(1 - q l ^ n)⁻¹‖ = 1 := by
  rw [norm_inv, denominator_norm_eq_one l hn, inv_one]

theorem denominator_sub_one_norm_lt_one {n : ℕ} (hn : 0 < n) :
    ‖(q l ^ n)‖ < ‖(1 : ℚ_[l.value])‖ := by
  simpa using q_power_norm_lt_one l hn

end BasicParameter

section NaturalCoefficientNorms

theorem nat_cast_norm_le_one (n : ℕ) :
    ‖(n : ℚ_[l.value])‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := Padic.nonarchimedean (p := l.value)
        (n : ℚ_[l.value]) (1 : ℚ_[l.value])
      calc
        ‖((Nat.succ n : ℕ) : ℚ_[l.value])‖ =
            ‖(n : ℚ_[l.value]) + 1‖ := by simp [Nat.cast_succ]
        _ ≤ max ‖(n : ℚ_[l.value])‖ ‖(1 : ℚ_[l.value])‖ := h
        _ ≤ 1 := max_le ih (by simp)

theorem nat_cast_norm_nonneg (n : ℕ) :
    0 ≤ ‖(n : ℚ_[l.value])‖ := norm_nonneg _

theorem nat_cast_power_norm_le_one (n weight : ℕ) :
    ‖(n : ℚ_[l.value])‖ ^ weight ≤ 1 := by
  exact pow_le_one₀ (norm_nonneg (n : ℚ_[l.value]))
    (nat_cast_norm_le_one l n)

theorem nat_cast_power_norm_nonneg (n weight : ℕ) :
    0 ≤ ‖(n : ℚ_[l.value]) ^ weight‖ := norm_nonneg _

theorem norm_five_le_one : ‖(5 : ℚ_[l.value])‖ ≤ 1 :=
  nat_cast_norm_le_one l 5

theorem norm_seven_le_one : ‖(7 : ℚ_[l.value])‖ ≤ 1 :=
  nat_cast_norm_le_one l 7

theorem norm_twelve_eq_one : ‖(12 : ℚ_[l.value])‖ = 1 := by
  have hp3 : ¬ l.value ∣ 3 := by
    intro h
    have hle := Nat.le_of_dvd (by norm_num : 0 < 3) h
    have hfive := l.ge_five
    omega
  have hp4 : ¬ l.value ∣ 4 := by
    intro h
    have hle := Nat.le_of_dvd (by norm_num : 0 < 4) h
    have hfive := l.ge_five
    omega
  have hc3 : Nat.Coprime l.value 3 :=
    l.prime.coprime_iff_not_dvd.mpr hp3
  have hc4 : Nat.Coprime l.value 4 :=
    l.prime.coprime_iff_not_dvd.mpr hp4
  have hc12 : Nat.Coprime l.value 12 := by
    simpa using hc3.mul_right hc4
  exact (Padic.norm_natCast_eq_one_iff (p := l.value) (n := 12)).mpr hc12

theorem norm_twelve_pos : 0 < ‖(12 : ℚ_[l.value])‖ := by
  rw [norm_twelve_eq_one l]
  norm_num

theorem norm_twelve_ne_zero : ‖(12 : ℚ_[l.value])‖ ≠ 0 :=
  ne_of_gt (norm_twelve_pos l)

theorem norm_five_pos : 0 < ‖(5 : ℚ_[l.value])‖ := by
  exact norm_pos_iff.mpr (by norm_num)

theorem norm_seven_pos : 0 < ‖(7 : ℚ_[l.value])‖ := by
  exact norm_pos_iff.mpr (by norm_num)

end NaturalCoefficientNorms

section LambertTerms

def term (weight n : ℕ) : ℚ_[l.value] :=
  if 0 < n then
    (n : ℚ_[l.value]) ^ weight * q l ^ n / (1 - q l ^ n)
  else 0

def series (weight : ℕ) : ℚ_[l.value] :=
  ∑' n : ℕ, term l weight n

@[simp] theorem term_zero (weight : ℕ) : term l weight 0 = 0 := by
  simp [term]

theorem term_eq_of_pos {n weight : ℕ} (hn : 0 < n) :
    term l weight n =
      (n : ℚ_[l.value]) ^ weight * q l ^ n / (1 - q l ^ n) := by
  simp [term, hn]

theorem term_eq_of_not_pos {n weight : ℕ} (hn : ¬ 0 < n) :
    term l weight n = 0 := by
  simp [term, hn]

theorem term_one (weight : ℕ) :
    term l weight 1 = q l / (1 - q l) := by
  rw [term_eq_of_pos l (by norm_num)]
  norm_num

theorem term_nonzero_one : term l 0 1 ≠ 0 := by
  rw [term_one]
  have hd : 1 - q l ≠ 0 := by
    simpa using (denominator_ne_zero l (n := 1) (by norm_num))
  exact div_ne_zero (q_ne_zero l) hd

theorem term_summable (weight : ℕ) :
    Summable (fun n : ℕ => term l weight n) := by
  simpa [term, q] using
    (TateCurve.lambertSeries_summable_from_one (K := ℚ_[l.value])
      (weight := weight) (Padic.norm_p_lt_one (p := l.value)))

theorem series_eq_lambertSeries (weight : ℕ) :
    series l weight = TateCurve.lambertSeries ℚ_[l.value] weight (q l) := by
  apply tsum_congr
  intro n
  by_cases hn : 0 < n
  · rw [term_eq_of_pos l hn]
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hn0
    simp [term, q]

theorem series_eq_lambertSeries_at_prime (weight : ℕ) :
    series l weight = TateCurve.lambertSeries ℚ_[l.value] weight
      (l.value : ℚ_[l.value]) := by
  simpa [q] using series_eq_lambertSeries l weight

theorem term_norm_le_q_power {n weight : ℕ} (hn : 0 < n) :
    ‖term l weight n‖ ≤ ‖q l ^ n‖ := by
  rw [term_eq_of_pos l hn, norm_div, norm_mul, norm_pow,
    denominator_norm_eq_one l hn, div_one]
  exact mul_le_of_le_one_left (norm_nonneg (q l ^ n))
    (nat_cast_power_norm_le_one l n weight)

theorem term_norm_le_geometric (n weight : ℕ) :
    ‖term l weight n‖ ≤ ‖q l‖ ^ n := by
  by_cases hn : 0 < n
  · exact (term_norm_le_q_power l hn).trans_eq (q_power_norm_eq l n)
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst hn0
    simp [term]

theorem term_norm_eq_q_power_one (weight : ℕ) :
    ‖term l weight 1‖ = ‖q l‖ := by
  rw [term_one]
  have hd : ‖1 - q l‖ = 1 := by
    simpa using (denominator_norm_eq_one l (n := 1) (by norm_num))
  rw [norm_div, hd, div_one]

theorem term_norm_nonneg (weight n : ℕ) : 0 ≤ ‖term l weight n‖ :=
  norm_nonneg _

theorem term_zero_is_the_only_zero_index (weight n : ℕ) (hn : 0 < n) :
    term l weight n =
      (n : ℚ_[l.value]) ^ weight * q l ^ n / (1 - q l ^ n) :=
  term_eq_of_pos l hn

theorem term_norm_lt_one (weight n : ℕ) (hn : 0 < n) :
    ‖term l weight n‖ < 1 := by
  calc
    ‖term l weight n‖ ≤ ‖q l‖ ^ n := term_norm_le_geometric l n weight
    _ = ‖q l ^ n‖ := (q_power_norm_eq l n).symm
    _ < 1 := q_power_norm_lt_one l hn

theorem term_is_integral_norm (weight n : ℕ) :
    ‖term l weight n‖ ≤ 1 := by
  by_cases hn : 0 < n
  · exact (term_norm_lt_one l weight n hn).le
  · simp [term, hn]

theorem term_norm_le_second_power {n weight : ℕ} (hn : 2 ≤ n) :
    ‖term l weight n‖ ≤ ‖q l‖ ^ 2 := by
  calc
    ‖term l weight n‖ ≤ ‖q l‖ ^ n := term_norm_le_geometric l n weight
    _ ≤ ‖q l‖ ^ 2 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add]
      exact mul_le_of_le_one_right (pow_nonneg (q_norm_nonneg l) _)
        (pow_le_one₀ (q_norm_nonneg l) (q_norm_lt_one l).le)

theorem term_norm_lt_first {n weight : ℕ} (hn : 2 ≤ n) :
    ‖term l weight n‖ < ‖q l‖ := by
  exact (term_norm_le_second_power l hn).trans_lt (by
    have hp := q_norm_pos l
    have hq := q_norm_lt_one l
    nlinarith)

end LambertTerms

section TailSeries

def tail (weight : ℕ) : ℚ_[l.value] :=
  ∑' k : ℕ, term l weight (k + 2)

def tailTerm (weight k : ℕ) : ℚ_[l.value] := term l weight (k + 2)

@[simp] theorem tailTerm_zero (weight : ℕ) :
    tailTerm l weight 0 = term l weight 2 := by
  rfl

theorem tailTerm_eq (weight k : ℕ) :
    tailTerm l weight k = term l weight (k + 2) := rfl

theorem tailTerm_norm_le (weight k : ℕ) :
    ‖tailTerm l weight k‖ ≤ ‖q l‖ ^ (k + 2) := by
  exact term_norm_le_geometric l (k + 2) weight

theorem geometric_summable (l : PrimeGeFive) [Fact (Nat.Prime l.value)] :
    Summable (fun n : ℕ => ‖q l‖ ^ n) := by
  exact summable_geometric_of_lt_one (q_norm_nonneg l) (q_norm_lt_one l)

theorem shifted_geometric_summable :
    Summable (fun k : ℕ => ‖q l‖ ^ (k + 2)) := by
  exact ((geometric_summable l).mul_left (‖q l‖ ^ 2)).congr
    (fun k => by
      rw [pow_add]
      ring)

theorem tail_norm_summable (weight : ℕ) :
    Summable (fun k : ℕ => ‖tailTerm l weight k‖) := by
  apply (shifted_geometric_summable l).of_norm_bounded_eventually_nat
  filter_upwards [] with k
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    (tailTerm_norm_le l weight k)

theorem tail_norm_le_geometric (weight : ℕ) :
    ‖tail l weight‖ ≤ ∑' k : ℕ, ‖q l‖ ^ (k + 2) := by
  exact (norm_tsum_le_tsum_norm (tail_norm_summable l weight)).trans
    ((tail_norm_summable l weight).tsum_le_tsum
      (fun k => tailTerm_norm_le l weight k)
      (shifted_geometric_summable l))

theorem shifted_geometric_sum :
    (∑' k : ℕ, ‖q l‖ ^ (k + 2)) =
      ‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹ := by
  calc
    (∑' k : ℕ, ‖q l‖ ^ (k + 2)) =
        ∑' k : ℕ, ‖q l‖ ^ 2 * ‖q l‖ ^ k := by
          apply tsum_congr
          intro k
          rw [pow_add]
          ring
    _ = ‖q l‖ ^ 2 * (∑' k : ℕ, ‖q l‖ ^ k) := tsum_mul_left
    _ = ‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹ := by
          rw [tsum_geometric_of_lt_one (q_norm_nonneg l) (q_norm_lt_one l)]

theorem tail_norm_le_closed (weight : ℕ) :
    ‖tail l weight‖ ≤ ‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹ := by
  rw [← shifted_geometric_sum l]
  exact tail_norm_le_geometric l weight

theorem tail_norm_lt_first (weight : ℕ) :
    ‖tail l weight‖ < ‖q l‖ := by
  have hr := q_norm_lt_half l
  have hden : 0 < 1 - ‖q l‖ := sub_pos.mpr (q_norm_lt_one l)
  have hfrac : ‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹ < ‖q l‖ := by
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ hden).2
    nlinarith [q_norm_pos l, q_norm_lt_half l]
  exact (tail_norm_le_closed l weight).trans_lt hfrac

theorem tail_norm_lt_one (weight : ℕ) : ‖tail l weight‖ < 1 := by
  exact (tail_norm_lt_first l weight).trans (q_norm_lt_one l)

theorem tail_ne_zero_or_zero (weight : ℕ) :
    tail l weight = 0 ∨ tail l weight ≠ 0 :=
  eq_or_ne (tail l weight) 0

theorem series_eq_first_plus_tail (weight : ℕ) :
    series l weight = term l weight 1 + tail l weight := by
  let f : ℕ → ℚ_[l.value] := fun n => term l weight n
  have hs : Summable f := by
    simpa [f] using term_summable l weight
  have hshift := (hasSum_nat_add_iff' 2).mpr hs.hasSum
  have htail : ∑' k : ℕ, f (k + 2) =
      (∑' n : ℕ, f n) - ∑ i ∈ Finset.range 2, f i := hshift.tsum_eq
  rw [show series l weight = ∑' n : ℕ, f n by rfl]
  rw [show tail l weight = ∑' k : ℕ, f (k + 2) by rfl]
  rw [htail]
  simp [f, Finset.sum_range_succ]

theorem series_norm_eq_first (weight : ℕ) :
    ‖series l weight‖ = ‖q l‖ := by
  rw [series_eq_first_plus_tail l weight]
  have htail := tail_norm_lt_first l weight
  have hne : ‖term l weight 1‖ ≠ ‖tail l weight‖ := by
    rw [term_norm_eq_q_power_one l weight]
    exact ne_of_gt htail
  rw [Padic.add_eq_max_of_ne hne]
  rw [term_norm_eq_q_power_one, max_eq_left (le_of_lt htail)]

theorem series_ne_zero (weight : ℕ) : series l weight ≠ 0 := by
  intro h
  have hn := series_norm_eq_first l weight
  rw [h, norm_zero] at hn
  exact (ne_of_gt (q_norm_pos l)) hn.symm

theorem tail_norm_formula_bound (weight : ℕ) :
    ‖tail l weight‖ ≤ ‖q l‖ ^ 2 / (1 - ‖q l‖) := by
  simpa [div_eq_mul_inv] using tail_norm_le_closed l weight

theorem tail_as_shifted_series (weight : ℕ) :
    tail l weight = ∑' k : ℕ, term l weight (k + 2) := rfl

theorem series_first_term_nonzero (weight : ℕ) :
    term l weight 1 ≠ 0 := by
  rw [term_one]
  have hd : 1 - q l ≠ 0 := by
    simpa using (denominator_ne_zero l (n := 1) (by norm_num))
  exact div_ne_zero (q_ne_zero l) hd

end TailSeries

section PrincipalCoefficients

def principal (weight : ℕ) : ℚ_[l.value] := term l weight 1

@[simp] theorem principal_eq (weight : ℕ) :
    principal l weight = q l / (1 - q l) := term_one l weight

theorem principal_norm (weight : ℕ) : ‖principal l weight‖ = ‖q l‖ := by
  exact term_norm_eq_q_power_one l weight

theorem principal_ne_zero (weight : ℕ) : principal l weight ≠ 0 := by
  exact series_first_term_nonzero l weight

theorem coefficient_series_decomposition (weight : ℕ) :
    series l weight = principal l weight + tail l weight := by
  exact series_eq_first_plus_tail l weight

theorem coefficient_series_norm (weight : ℕ) : ‖series l weight‖ = ‖principal l weight‖ := by
  rw [series_norm_eq_first l weight, principal_norm l weight]

def a4Principal : ℚ_[l.value] :=
  -(5 : ℚ_[l.value]) * principal l 3

def a4Remainder : ℚ_[l.value] :=
  -(5 : ℚ_[l.value]) * tail l 3

theorem a4_decomposition :
    TateCurve.a4 ℚ_[l.value] (q l) = a4Principal l + a4Remainder l := by
  rw [TateCurve.a4, ← series_eq_lambertSeries l 3]
  rw [coefficient_series_decomposition l 3]
  simp [a4Principal, a4Remainder]
  ring

theorem a4_remainder_norm_le :
    ‖a4Remainder l‖ ≤ ‖(5 : ℚ_[l.value])‖ *
      (‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹) := by
  simp only [a4Remainder, norm_neg, norm_mul]
  exact mul_le_mul_of_nonneg_left (tail_norm_le_closed l 3)
    (norm_nonneg _)

theorem a4_remainder_norm_lt_principal :
    ‖a4Remainder l‖ < ‖a4Principal l‖ := by
  have h := tail_norm_lt_first l 3
  simp only [a4Remainder, a4Principal, norm_neg, norm_mul, principal_norm]
  exact mul_lt_mul_of_pos_left h (norm_five_pos l)

theorem a4_principal_norm : ‖a4Principal l‖ =
    ‖(5 : ℚ_[l.value])‖ * ‖q l‖ := by
  simp only [a4Principal, norm_neg, norm_mul, principal_norm]

theorem a4_norm_eq :
    ‖TateCurve.a4 ℚ_[l.value] (q l)‖ =
      ‖(5 : ℚ_[l.value])‖ * ‖q l‖ := by
  rw [a4_decomposition l]
  have hne : ‖a4Principal l‖ ≠ ‖a4Remainder l‖ :=
    ne_of_gt (a4_remainder_norm_lt_principal l)
  rw [Padic.add_eq_max_of_ne hne, max_eq_left
    (le_of_lt (a4_remainder_norm_lt_principal l)), a4_principal_norm]

theorem a4_ne_zero : TateCurve.a4 ℚ_[l.value] (q l) ≠ 0 := by
  intro h
  have hn := a4_norm_eq l
  rw [h, norm_zero] at hn
  have hp : 0 < ‖(5 : ℚ_[l.value])‖ * ‖q l‖ :=
    mul_pos (norm_five_pos l) (q_norm_pos l)
  exact (ne_of_gt hp) hn.symm

def a6Principal : ℚ_[l.value] :=
  -(q l / (1 - q l))

def a6Remainder : ℚ_[l.value] :=
  -((5 : ℚ_[l.value]) * tail l 3 + (7 : ℚ_[l.value]) * tail l 5) / 12

theorem a6_decomposition :
    TateCurve.a6 ℚ_[l.value] (q l) = a6Principal l + a6Remainder l := by
  rw [TateCurve.a6, ← series_eq_lambertSeries l 3,
    ← series_eq_lambertSeries l 5]
  rw [coefficient_series_decomposition l 3,
    coefficient_series_decomposition l 5]
  simp [a6Principal, a6Remainder, principal_eq]
  field_simp
  ring

theorem a6_principal_norm : ‖a6Principal l‖ = ‖q l‖ := by
  rw [a6Principal, norm_neg, norm_div]
  have hd : ‖1 - q l‖ = 1 := by
    simpa using (denominator_norm_eq_one l (n := 1) (by norm_num))
  rw [hd, div_one]

theorem a6_remainder_norm_le :
    ‖a6Remainder l‖ ≤ ‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹ := by
  rw [a6Remainder, norm_div, norm_neg]
  have h3 := tail_norm_le_closed l 3
  have h5 := tail_norm_le_closed l 5
  have h5' : ‖(5 : ℚ_[l.value]) * tail l 3‖ ≤
      ‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg (tail l 3))
      (norm_five_le_one l)).trans h3
  have h7' : ‖(7 : ℚ_[l.value]) * tail l 5‖ ≤
      ‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg (tail l 5))
      (norm_seven_le_one l)).trans h5
  have hmax := max_le h5' h7'
  have hadd := Padic.nonarchimedean (p := l.value)
    ((5 : ℚ_[l.value]) * tail l 3)
    ((7 : ℚ_[l.value]) * tail l 5)
  have hsum : ‖(5 : ℚ_[l.value]) * tail l 3 +
      (7 : ℚ_[l.value]) * tail l 5‖ ≤
      ‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹ :=
    hadd.trans hmax
  rw [norm_twelve_eq_one l, div_one]
  exact hsum

theorem a6_remainder_norm_lt_principal :
    ‖a6Remainder l‖ < ‖a6Principal l‖ := by
  have hfrac : ‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹ < ‖q l‖ := by
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ (sub_pos.mpr (q_norm_lt_one l))).2
    nlinarith [q_norm_pos l, q_norm_lt_half l]
  have hrem : ‖a6Remainder l‖ < ‖q l‖ :=
    (a6_remainder_norm_le l).trans_lt hfrac
  exact hrem.trans_eq (a6_principal_norm l).symm

theorem a6_norm_eq :
    ‖TateCurve.a6 ℚ_[l.value] (q l)‖ = ‖q l‖ := by
  rw [a6_decomposition l]
  have hne : ‖a6Principal l‖ ≠ ‖a6Remainder l‖ :=
    ne_of_gt (a6_remainder_norm_lt_principal l)
  rw [Padic.add_eq_max_of_ne hne, max_eq_left
    (le_of_lt (a6_remainder_norm_lt_principal l)), a6_principal_norm]

theorem a6_ne_zero : TateCurve.a6 ℚ_[l.value] (q l) ≠ 0 := by
  intro h
  have hn := a6_norm_eq l
  rw [h, norm_zero] at hn
  exact (ne_of_gt (q_norm_pos l)) hn.symm

end PrincipalCoefficients

section C4Nondegeneracy

theorem a4_norm_lt_one :
    ‖TateCurve.a4 ℚ_[l.value] (q l)‖ < 1 := by
  rw [a4_norm_eq l]
  calc
    ‖(5 : ℚ_[l.value])‖ * ‖q l‖ ≤ 1 * ‖q l‖ := by
      exact mul_le_mul_of_nonneg_right (norm_five_le_one l) (q_norm_nonneg l)
    _ = ‖q l‖ := one_mul _
    _ < 1 := q_norm_lt_one l

theorem a4_scaled_norm_lt_one :
    ‖(48 : ℚ_[l.value]) * TateCurve.a4 ℚ_[l.value] (q l)‖ < 1 := by
  rw [norm_mul]
  have h48 : ‖(48 : ℚ_[l.value])‖ ≤ 1 := nat_cast_norm_le_one l 48
  calc
    ‖(48 : ℚ_[l.value])‖ *
        ‖TateCurve.a4 ℚ_[l.value] (q l)‖ ≤
        ‖TateCurve.a4 ℚ_[l.value] (q l)‖ := by
      simpa [mul_comm] using
        (mul_le_of_le_one_right
          (norm_nonneg (TateCurve.a4 ℚ_[l.value] (q l))) h48)
    _ < 1 := a4_norm_lt_one l

theorem c4_norm_eq_one :
    ‖(TateCurve.weierstrassCurve ℚ_[l.value] (q l)).c₄‖ = 1 := by
  rw [TateCurve.canonical_c₄]
  have hprod := a4_scaled_norm_lt_one l
  have hneq : ‖(1 : ℚ_[l.value])‖ ≠
      ‖-(48 : ℚ_[l.value]) * TateCurve.a4 ℚ_[l.value] (q l)‖ := by
    simpa [norm_one, norm_neg, mul_comm] using (ne_of_gt hprod)
  rw [show (1 : ℚ_[l.value]) - 48 *
      TateCurve.a4 ℚ_[l.value] (q l) =
      1 + -(48 * TateCurve.a4 ℚ_[l.value] (q l)) by ring]
  calc
    ‖1 + -(48 * TateCurve.a4 ℚ_[l.value] (q l))‖ =
        ‖1 + -(48 : ℚ_[l.value]) * TateCurve.a4 ℚ_[l.value] (q l)‖ := by
          congr 1; ring
    _ = max ‖(1 : ℚ_[l.value])‖
        ‖-(48 : ℚ_[l.value]) * TateCurve.a4 ℚ_[l.value] (q l)‖ :=
      Padic.add_eq_max_of_ne hneq
    _ = 1 := by
      have hle : ‖-(48 : ℚ_[l.value]) *
          TateCurve.a4 ℚ_[l.value] (q l)‖ ≤ 1 := by
        simpa [norm_neg, mul_comm] using hprod.le
      simpa only [norm_one] using (max_eq_left hle)

theorem c4_ne_zero :
    (TateCurve.weierstrassCurve ℚ_[l.value] (q l)).c₄ ≠ 0 := by
  intro h
  have hn := c4_norm_eq_one l
  rw [h, norm_zero] at hn
  norm_num at hn

theorem c4_is_unit : IsUnit
    (TateCurve.weierstrassCurve ℚ_[l.value] (q l)).c₄ := by
  exact isUnit_iff_ne_zero.mpr (c4_ne_zero l)

theorem canonical_coefficients_nonzero :
    TateCurve.a4 ℚ_[l.value] (q l) ≠ 0 ∧
      TateCurve.a6 ℚ_[l.value] (q l) ≠ 0 ∧
      (TateCurve.weierstrassCurve ℚ_[l.value] (q l)).c₄ ≠ 0 := by
  exact ⟨a4_ne_zero l, a6_ne_zero l, c4_ne_zero l⟩

end C4Nondegeneracy

section AuditBoundary

section FiniteTruncations

def partialSum (weight N : ℕ) : ℚ_[l.value] :=
  ∑ n ∈ Finset.range N, term l weight n

def shiftedTail (weight N : ℕ) : ℚ_[l.value] :=
  ∑' k : ℕ, term l weight (k + N)

@[simp] theorem partialSum_zero (weight : ℕ) :
    partialSum l weight 0 = 0 := by
  simp [partialSum]

@[simp] theorem partialSum_one (weight : ℕ) :
    partialSum l weight 1 = term l weight 0 := by
  simp [partialSum]

theorem partialSum_succ (weight N : ℕ) :
    partialSum l weight (N + 1) =
      partialSum l weight N + term l weight N := by
  rw [partialSum, partialSum, Finset.sum_range_succ]

theorem partialSum_two (weight : ℕ) :
    partialSum l weight 2 = term l weight 1 := by
  rw [partialSum_succ, partialSum_one, term_zero]
  simp

theorem partialSum_three (weight : ℕ) :
    partialSum l weight 3 = term l weight 1 + term l weight 2 := by
  rw [partialSum_succ, partialSum_two]

theorem partialSum_nonempty (weight N : ℕ) :
    partialSum l weight (N + 1) =
      partialSum l weight N + term l weight N :=
  partialSum_succ l weight N

theorem shiftedTail_zero (weight : ℕ) :
    shiftedTail l weight 0 = series l weight := by
  rfl

theorem shiftedTail_two (weight : ℕ) :
    shiftedTail l weight 2 = tail l weight := by
  rfl

theorem shiftedTail_summable (weight N : ℕ) :
    Summable (fun k : ℕ => term l weight (k + N)) := by
  have hgeom : Summable (fun k : ℕ => ‖q l‖ ^ (k + N)) := by
    simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using
      (geometric_summable l).mul_left (‖q l‖ ^ N)
  refine hgeom.of_norm_bounded_eventually_nat
    (f := fun k : ℕ => term l weight (k + N)) ?_
  filter_upwards [] with k
  exact term_norm_le_geometric l (k + N) weight

set_option maxHeartbeats 800000 in
-- The finite-shift geometric comparison unfolds several normed-series
-- coercions; the higher budget is for elaboration only, not an axiom.
theorem shiftedTail_norm_le_geometric (weight N : ℕ) :
    ‖shiftedTail l weight N‖ ≤
      ∑' k : ℕ, ‖q l‖ ^ (k + N) := by
  have hnorm : Summable (fun k : ℕ =>
      ‖term l weight (k + N)‖) := by
    have hgeom : Summable (fun k : ℕ => ‖q l‖ ^ (k + N)) := by
      simpa [pow_add, mul_comm] using
        (geometric_summable l).mul_left (‖q l‖ ^ N)
    exact hgeom.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => term_norm_le_geometric l (k + N) weight)
  exact (norm_tsum_le_tsum_norm hnorm).trans
    (hnorm.tsum_le_tsum
      (fun k => term_norm_le_geometric l (k + N) weight)
      (by
        simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using
          (geometric_summable l).mul_left (‖q l‖ ^ N)))

theorem shiftedTail_norm_le_closed (weight N : ℕ) :
    ‖shiftedTail l weight N‖ ≤
      ‖q l‖ ^ N * (1 - ‖q l‖)⁻¹ := by
  have hsum : (∑' k : ℕ, ‖q l‖ ^ (k + N)) =
      ‖q l‖ ^ N * (1 - ‖q l‖)⁻¹ := by
    calc
      (∑' k : ℕ, ‖q l‖ ^ (k + N)) =
          ∑' k : ℕ, ‖q l‖ ^ N * ‖q l‖ ^ k := by
            apply tsum_congr
            intro k
            rw [pow_add]
            ring
      _ = ‖q l‖ ^ N * (∑' k : ℕ, ‖q l‖ ^ k) := tsum_mul_left
      _ = ‖q l‖ ^ N * (1 - ‖q l‖)⁻¹ := by
            rw [tsum_geometric_of_lt_one (q_norm_nonneg l)
              (q_norm_lt_one l)]
  rw [← hsum]
  exact shiftedTail_norm_le_geometric l weight N

theorem shiftedTail_norm_lt_first_of_two_le {N weight : ℕ}
    (hN : 2 ≤ N) : ‖shiftedTail l weight N‖ < ‖q l‖ := by
  have hNpow : ‖q l‖ ^ N ≤ ‖q l‖ ^ 2 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [pow_add]
    exact mul_le_of_le_one_right (pow_nonneg (q_norm_nonneg l) _)
      (pow_le_one₀ (q_norm_nonneg l) (q_norm_lt_one l).le)
  have hclosed := shiftedTail_norm_le_closed l weight N
  have hfrac : ‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹ < ‖q l‖ := by
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ (sub_pos.mpr (q_norm_lt_one l))).2
    nlinarith [q_norm_pos l, q_norm_lt_half l]
  exact (hclosed.trans (mul_le_mul_of_nonneg_right hNpow
    (inv_nonneg.mpr (sub_nonneg.mpr (q_norm_lt_one l).le)))).trans_lt hfrac

theorem series_eq_partialSum_add_shiftedTail (weight N : ℕ) :
    series l weight = partialSum l weight N + shiftedTail l weight N := by
  let f : ℕ → ℚ_[l.value] := fun n => term l weight n
  have hs : Summable f := by
    simpa [f] using term_summable l weight
  have hshift := (hasSum_nat_add_iff' N).mpr hs.hasSum
  have htail : ∑' k : ℕ, f (k + N) =
      (∑' n : ℕ, f n) - ∑ i ∈ Finset.range N, f i := hshift.tsum_eq
  rw [show series l weight = ∑' n : ℕ, f n by rfl]
  rw [show partialSum l weight N = ∑ i ∈ Finset.range N, f i by rfl]
  rw [show shiftedTail l weight N = ∑' k : ℕ, f (k + N) by rfl]
  rw [htail]
  ring

theorem series_eq_partialSum_add_tail_two (weight : ℕ) :
    series l weight = partialSum l weight 2 + shiftedTail l weight 2 :=
by
  exact series_eq_partialSum_add_shiftedTail l weight 2

theorem series_remainder_after_two_norm_lt (weight : ℕ) :
    ‖series l weight - partialSum l weight 2‖ < ‖q l‖ := by
  rw [series_eq_partialSum_add_tail_two l weight]
  simp only [add_sub_cancel_left]
  exact shiftedTail_norm_lt_first_of_two_le l (by norm_num)

theorem partialSum_norm_le_geometric (weight N : ℕ) :
    ‖partialSum l weight N‖ ≤ ∑ n ∈ Finset.range N, ‖q l‖ ^ n := by
  rw [partialSum]
  calc
    ‖∑ n ∈ Finset.range N, term l weight n‖ ≤
        ∑ n ∈ Finset.range N, ‖term l weight n‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, ‖q l‖ ^ n := by
      exact Finset.sum_le_sum fun n hn => term_norm_le_geometric l n weight

theorem partialSum_term_norm_nonnegative (weight N : ℕ) :
    0 ≤ ∑ n ∈ Finset.range N, ‖term l weight n‖ := by
  exact Finset.sum_nonneg fun n hn => term_norm_nonneg l weight n

theorem shiftedTail_zero_term_is_irrelevant (weight N : ℕ) :
    shiftedTail l weight N =
      ∑' k : ℕ, if 0 < k + N then term l weight (k + N) else 0 := by
  apply tsum_congr
  intro k
  by_cases hk : 0 < k + N
  · simp [hk]
  · simp [term, hk]

theorem finite_first_two_exact (weight : ℕ) :
    partialSum l weight 2 = principal l weight := by
  rw [partialSum_two, principal]

end FiniteTruncations

section CoefficientIdentities

theorem a4_series_identity :
    TateCurve.a4 ℚ_[l.value] (q l) = -(5 : ℚ_[l.value]) * series l 3 := by
  rw [TateCurve.a4, series_eq_lambertSeries l 3]

theorem a6_series_identity :
    TateCurve.a6 ℚ_[l.value] (q l) =
      -((5 : ℚ_[l.value]) * series l 3 +
        (7 : ℚ_[l.value]) * series l 5) / 12 := by
  rw [TateCurve.a6, series_eq_lambertSeries l 3,
    series_eq_lambertSeries l 5]

theorem a4_principal_identity :
    a4Principal l = -(5 : ℚ_[l.value]) * (q l / (1 - q l)) := by
  simp [a4Principal, principal_eq]

theorem a4_remainder_identity :
    a4Remainder l = -(5 : ℚ_[l.value]) * tail l 3 := rfl

theorem a6_principal_identity :
    a6Principal l = -(q l / (1 - q l)) := rfl

theorem a6_remainder_identity :
    a6Remainder l =
      -((5 : ℚ_[l.value]) * tail l 3 +
        (7 : ℚ_[l.value]) * tail l 5) / 12 := rfl

theorem a4_is_principal_plus_explicit_tail :
    TateCurve.a4 ℚ_[l.value] (q l) =
      -(5 : ℚ_[l.value]) * (q l / (1 - q l)) + a4Remainder l := by
  rw [a4_decomposition l, a4_principal_identity l]

theorem a6_is_principal_plus_explicit_tail :
    TateCurve.a6 ℚ_[l.value] (q l) =
      -(q l / (1 - q l)) + a6Remainder l := by
  rw [a6_decomposition l, a6_principal_identity l]

theorem a4_difference_from_principal :
    TateCurve.a4 ℚ_[l.value] (q l) - a4Principal l = a4Remainder l := by
  rw [a4_decomposition l]
  ring

theorem a6_difference_from_principal :
    TateCurve.a6 ℚ_[l.value] (q l) - a6Principal l = a6Remainder l := by
  rw [a6_decomposition l]
  ring

theorem a4_principal_norm_closed :
    ‖a4Principal l‖ = ‖(5 : ℚ_[l.value])‖ * ‖q l‖ :=
  a4_principal_norm l

theorem a6_principal_norm_closed :
    ‖a6Principal l‖ = ‖q l‖ :=
  a6_principal_norm l

theorem a4_remainder_strictly_smaller :
    ‖a4Remainder l‖ < ‖a4Principal l‖ :=
  a4_remainder_norm_lt_principal l

theorem a6_remainder_strictly_smaller :
    ‖a6Remainder l‖ < ‖a6Principal l‖ :=
  a6_remainder_norm_lt_principal l

theorem a4_norm_is_principal_norm :
    ‖TateCurve.a4 ℚ_[l.value] (q l)‖ = ‖a4Principal l‖ := by
  rw [a4_norm_eq l, a4_principal_norm]

theorem a6_norm_is_principal_norm :
    ‖TateCurve.a6 ℚ_[l.value] (q l)‖ = ‖a6Principal l‖ := by
  rw [a6_norm_eq l, a6_principal_norm]

theorem a4_is_not_equal_to_zero_series :
    TateCurve.a4 ℚ_[l.value] (q l) ≠ 0 := a4_ne_zero l

theorem a6_is_not_equal_to_zero_series :
    TateCurve.a6 ℚ_[l.value] (q l) ≠ 0 := a6_ne_zero l

theorem c4_formula_at_q :
    (TateCurve.weierstrassCurve ℚ_[l.value] (q l)).c₄ =
      1 - 48 * TateCurve.a4 ℚ_[l.value] (q l) := by
  exact TateCurve.canonical_c₄ (q l)

theorem c4_formula_at_prime :
    (TateCurve.weierstrassCurve ℚ_[l.value] (q l)).c₄ =
      1 - 48 * TateCurve.a4 ℚ_[l.value] (l.value : ℚ_[l.value]) := by
  simpa [q] using c4_formula_at_q l

theorem c4_unit_from_principal_estimate :
    IsUnit (TateCurve.weierstrassCurve ℚ_[l.value] (q l)).c₄ :=
  c4_is_unit l

end CoefficientIdentities

section CertifiedConsequences

theorem all_positive_lambert_terms_contract (weight n : ℕ) (hn : 0 < n) :
    ‖term l weight n‖ < 1 := term_norm_lt_one l weight n hn

theorem all_lambert_terms_are_bounded (weight n : ℕ) :
    ‖term l weight n‖ ≤ 1 := term_is_integral_norm l weight n

theorem tail_after_any_two_terms_is_small (weight N : ℕ)
    (hN : 2 ≤ N) : ‖shiftedTail l weight N‖ < ‖q l‖ :=
  shiftedTail_norm_lt_first_of_two_le l hN

theorem second_and_later_terms_are_strictly_smaller (weight n : ℕ)
    (hn : 2 ≤ n) : ‖term l weight n‖ < ‖q l‖ :=
  term_norm_lt_first l hn

theorem canonical_a4_a6_c4_have_nonzero_certificates :
    TateCurve.a4 ℚ_[l.value] (q l) ≠ 0 ∧
      TateCurve.a6 ℚ_[l.value] (q l) ≠ 0 ∧
      (TateCurve.weierstrassCurve ℚ_[l.value] (q l)).c₄ ≠ 0 :=
  canonical_coefficients_nonzero l

theorem canonical_c4_is_unit_certificate :
    IsUnit (TateCurve.weierstrassCurve ℚ_[l.value] (q l)).c₄ :=
  c4_is_unit l

end CertifiedConsequences

section WeierstrassArithmeticAtQ

def canonicalCurve : WeierstrassCurve ℚ_[l.value] :=
  TateCurve.weierstrassCurve ℚ_[l.value] (q l)

theorem canonicalCurve_eq :
    canonicalCurve l = TateCurve.weierstrassCurve ℚ_[l.value] (q l) := rfl

theorem canonicalCurve_a1 : (canonicalCurve l).a₁ = 1 := by
  exact TateCurve.canonical_a₁ (q l)

theorem canonicalCurve_a2 : (canonicalCurve l).a₂ = 0 := by
  exact TateCurve.canonical_a₂ (q l)

theorem canonicalCurve_a3 : (canonicalCurve l).a₃ = 0 := by
  exact TateCurve.canonical_a₃ (q l)

theorem canonicalCurve_a4 : (canonicalCurve l).a₄ =
    TateCurve.a4 ℚ_[l.value] (q l) := by
  exact TateCurve.canonical_a₄ (q l)

theorem canonicalCurve_a6 : (canonicalCurve l).a₆ =
    TateCurve.a6 ℚ_[l.value] (q l) := by
  exact TateCurve.canonical_a₆ (q l)

theorem canonicalCurve_b2 : (canonicalCurve l).b₂ = 1 := by
  exact TateCurve.canonical_b₂ (q l)

theorem canonicalCurve_b4 : (canonicalCurve l).b₄ =
    2 * TateCurve.a4 ℚ_[l.value] (q l) := by
  exact TateCurve.canonical_b₄ (q l)

theorem canonicalCurve_b6 : (canonicalCurve l).b₆ =
    4 * TateCurve.a6 ℚ_[l.value] (q l) := by
  exact TateCurve.canonical_b₆ (q l)

theorem canonicalCurve_b8 : (canonicalCurve l).b₈ =
    TateCurve.a6 ℚ_[l.value] (q l) -
      (TateCurve.a4 ℚ_[l.value] (q l)) ^ 2 := by
  exact TateCurve.canonical_b₈ (q l)

theorem canonicalCurve_b_relation :
    4 * (canonicalCurve l).b₈ =
      (canonicalCurve l).b₂ * (canonicalCurve l).b₆ -
        (canonicalCurve l).b₄ ^ 2 := by
  exact TateCurve.canonical_b_relation (q l)

theorem canonicalCurve_c4 : (canonicalCurve l).c₄ =
    1 - 48 * TateCurve.a4 ℚ_[l.value] (q l) := by
  exact TateCurve.canonical_c₄ (q l)

theorem canonicalCurve_c6 : (canonicalCurve l).c₆ =
    -1 + 72 * TateCurve.a4 ℚ_[l.value] (q l) -
      864 * TateCurve.a6 ℚ_[l.value] (q l) := by
  exact TateCurve.canonical_c₆ (q l)

theorem canonicalCurve_delta : (canonicalCurve l).Δ =
    (TateCurve.a4 ℚ_[l.value] (q l)) ^ 2 -
      TateCurve.a6 ℚ_[l.value] (q l) -
      64 * (TateCurve.a4 ℚ_[l.value] (q l)) ^ 3 -
      432 * (TateCurve.a6 ℚ_[l.value] (q l)) ^ 2 +
      72 * TateCurve.a4 ℚ_[l.value] (q l) *
        TateCurve.a6 ℚ_[l.value] (q l) := by
  exact TateCurve.canonical_delta (q l)

theorem canonicalCurve_c_relation :
    1728 * (canonicalCurve l).Δ =
      (canonicalCurve l).c₄ ^ 3 - (canonicalCurve l).c₆ ^ 2 := by
  exact TateCurve.canonical_c_relation (q l)

theorem canonicalCurve_delta_expanded_in_series :
    (canonicalCurve l).Δ =
      (TateCurve.a4 ℚ_[l.value] (q l)) ^ 2 -
        TateCurve.a6 ℚ_[l.value] (q l) -
        64 * (TateCurve.a4 ℚ_[l.value] (q l)) ^ 3 -
        432 * (TateCurve.a6 ℚ_[l.value] (q l)) ^ 2 +
        72 * TateCurve.a4 ℚ_[l.value] (q l) *
          TateCurve.a6 ℚ_[l.value] (q l) :=
  canonicalCurve_delta l

theorem canonicalCurve_c4_sub_one :
    (canonicalCurve l).c₄ - 1 =
      -48 * TateCurve.a4 ℚ_[l.value] (q l) := by
  rw [canonicalCurve_c4]
  ring

theorem canonicalCurve_c6_add_one :
    (canonicalCurve l).c₆ + 1 =
      72 * TateCurve.a4 ℚ_[l.value] (q l) -
        864 * TateCurve.a6 ℚ_[l.value] (q l) := by
  rw [canonicalCurve_c6]
  ring

theorem canonicalCurve_delta_as_b8_correction :
    (canonicalCurve l).Δ = -(canonicalCurve l).b₈ -
      8 * (canonicalCurve l).b₄ ^ 3 -
      27 * (canonicalCurve l).b₆ ^ 2 +
      9 * (canonicalCurve l).b₄ * (canonicalCurve l).b₆ := by
  exact TateCurve.canonical_delta_as_b₈_correction (q l)

theorem canonicalCurve_delta_ne_zero_iff_series :
    (canonicalCurve l).Δ ≠ 0 ↔
      (TateCurve.a4 ℚ_[l.value] (q l)) ^ 2 -
        TateCurve.a6 ℚ_[l.value] (q l) -
        64 * (TateCurve.a4 ℚ_[l.value] (q l)) ^ 3 -
        432 * (TateCurve.a6 ℚ_[l.value] (q l)) ^ 2 +
        72 * TateCurve.a4 ℚ_[l.value] (q l) *
          TateCurve.a6 ℚ_[l.value] (q l) ≠ 0 := by
  exact TateCurve.canonical_delta_ne_zero_iff (q l)

theorem canonicalCurve_delta_eq_zero_iff_series :
    (canonicalCurve l).Δ = 0 ↔
      (TateCurve.a4 ℚ_[l.value] (q l)) ^ 2 -
        TateCurve.a6 ℚ_[l.value] (q l) -
        64 * (TateCurve.a4 ℚ_[l.value] (q l)) ^ 3 -
        432 * (TateCurve.a6 ℚ_[l.value] (q l)) ^ 2 +
        72 * TateCurve.a4 ℚ_[l.value] (q l) *
          TateCurve.a6 ℚ_[l.value] (q l) = 0 := by
  exact TateCurve.canonical_delta_eq_zero_iff (q l)

theorem canonicalCurve_c4_unit : IsUnit (canonicalCurve l).c₄ :=
  c4_is_unit l

theorem canonicalCurve_c4_nonzero : (canonicalCurve l).c₄ ≠ 0 :=
  c4_ne_zero l

theorem canonicalCurve_a4_nonzero : (canonicalCurve l).a₄ ≠ 0 :=
  a4_ne_zero l

theorem canonicalCurve_a6_nonzero : (canonicalCurve l).a₆ ≠ 0 :=
  a6_ne_zero l

theorem canonicalCurve_is_elliptic_of_delta_ne_zero
    (hΔ : (canonicalCurve l).Δ ≠ 0) :
    (canonicalCurve l).IsElliptic := by
  exact TateCurve.canonical_is_elliptic_of_delta_ne_zero
    (q_norm_lt_one l) (q_ne_zero l) hΔ

theorem canonicalCurve_is_elliptic_iff_delta_ne_zero :
    (canonicalCurve l).IsElliptic ↔ (canonicalCurve l).Δ ≠ 0 := by
  exact TateCurve.canonical_is_elliptic_iff_delta_ne_zero

theorem canonicalCurve_delta_unit_iff :
    IsUnit (canonicalCurve l).Δ ↔ (canonicalCurve l).Δ ≠ 0 := by
  exact TateCurve.canonical_delta_unit_iff

theorem canonicalCurve_delta_nonzero_of_series_expansion
    (h : (TateCurve.a4 ℚ_[l.value] (q l)) ^ 2 -
      TateCurve.a6 ℚ_[l.value] (q l) -
      64 * (TateCurve.a4 ℚ_[l.value] (q l)) ^ 3 -
      432 * (TateCurve.a6 ℚ_[l.value] (q l)) ^ 2 +
      72 * TateCurve.a4 ℚ_[l.value] (q l) *
        TateCurve.a6 ℚ_[l.value] (q l) ≠ 0) :
    (canonicalCurve l).Δ ≠ 0 := by
  exact (canonicalCurve_delta_ne_zero_iff_series l).2 h

theorem canonicalCurve_delta_is_the_only_remaining_q_series_obligation :
    ((canonicalCurve l).Δ ≠ 0) ↔
      ((canonicalCurve l).IsElliptic) := by
  exact (canonicalCurve_is_elliptic_iff_delta_ne_zero l).symm

end WeierstrassArithmeticAtQ

section ExplicitNormTransport

theorem q_norm_sq_lt_q_norm : ‖q l‖ ^ 2 < ‖q l‖ := by
  have hp := q_norm_pos l
  have hq := q_norm_lt_one l
  nlinarith

theorem q_norm_fourth_lt_q_norm : ‖q l‖ ^ 4 < ‖q l‖ := by
  have hp := q_norm_pos l
  have hq := q_norm_lt_one l
  nlinarith [q_norm_sq_lt_q_norm l]

theorem q_norm_pow_monotone_from_two {m : ℕ} (hm : 2 ≤ m) :
    ‖q l‖ ^ m ≤ ‖q l‖ ^ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add]
  exact mul_le_of_le_one_right (pow_nonneg (q_norm_nonneg l) _)
    (pow_le_one₀ (q_norm_nonneg l) (q_norm_lt_one l).le)

theorem q_norm_pow_lt_one_from_one {m : ℕ} (hm : 0 < m) :
    ‖q l‖ ^ m < 1 := by
  exact pow_lt_one₀ (q_norm_nonneg l) (q_norm_lt_one l) hm.ne'

theorem q_norm_inverse_denominator_pos {m : ℕ} (hm : 0 < m) :
    0 < ‖(1 - q l ^ m)⁻¹‖ := by
  rw [denominator_inverse_norm_eq_one l hm]
  norm_num

theorem principal_norm_is_positive (weight : ℕ) :
    0 < ‖principal l weight‖ := by
  rw [principal_norm l]
  exact q_norm_pos l

theorem tail_norm_is_nonnegative (weight : ℕ) :
    0 ≤ ‖tail l weight‖ := norm_nonneg _

theorem tail_norm_is_strictly_less_than_one (weight : ℕ) :
    ‖tail l weight‖ < 1 := tail_norm_lt_one l weight

theorem a4_norm_is_strictly_positive :
    0 < ‖TateCurve.a4 ℚ_[l.value] (q l)‖ := by
  rw [a4_norm_eq l]
  exact mul_pos (norm_five_pos l) (q_norm_pos l)

theorem a6_norm_is_strictly_positive :
    0 < ‖TateCurve.a6 ℚ_[l.value] (q l)‖ := by
  rw [a6_norm_eq l]
  exact q_norm_pos l

theorem c4_norm_is_strictly_positive :
    0 < ‖(canonicalCurve l).c₄‖ := by
  change 0 < ‖(TateCurve.weierstrassCurve ℚ_[l.value] (q l)).c₄‖
  rw [c4_norm_eq_one l]
  norm_num

theorem c4_norm_is_not_zero :
    ‖(canonicalCurve l).c₄‖ ≠ 0 :=
  ne_of_gt (c4_norm_is_strictly_positive l)

end ExplicitNormTransport

section ConvergenceCertificates

theorem partialSum_error_norm_le (weight N : ℕ) :
    ‖series l weight - partialSum l weight N‖ ≤
      ‖q l‖ ^ N * (1 - ‖q l‖)⁻¹ := by
  rw [series_eq_partialSum_add_shiftedTail l weight N]
  simp only [add_sub_cancel_left]
  exact shiftedTail_norm_le_closed l weight N

theorem partialSum_error_norm_lt_first_after_two (weight : ℕ) :
    ‖series l weight - partialSum l weight 2‖ < ‖q l‖ := by
  exact series_remainder_after_two_norm_lt l weight

theorem partialSum_two_is_principal (weight : ℕ) :
    partialSum l weight 2 = principal l weight :=
  finite_first_two_exact l weight

theorem series_minus_principal_is_tail (weight : ℕ) :
    series l weight - principal l weight = tail l weight := by
  rw [series_eq_first_plus_tail l weight]
  simp [principal]

theorem principal_is_a_strict_approximation (weight : ℕ) :
    ‖series l weight - principal l weight‖ < ‖principal l weight‖ := by
  rw [series_minus_principal_is_tail l weight, principal_norm]
  exact tail_norm_lt_first l weight

theorem series_is_not_principal (weight : ℕ) :
    series l weight = principal l weight ↔ tail l weight = 0 := by
  rw [← sub_eq_zero, series_minus_principal_is_tail l weight]

theorem q_series_tail_certificate (weight : ℕ) :
    ‖tail l weight‖ ≤ ‖q l‖ ^ 2 / (1 - ‖q l‖) ∧
      ‖tail l weight‖ < ‖q l‖ :=
  ⟨tail_norm_formula_bound l weight, tail_norm_lt_first l weight⟩

end ConvergenceCertificates

section IntegralCoefficientWitnesses

def integralElement (x : ℚ_[l.value]) (hx : ‖x‖ ≤ 1) : ℤ_[l.value] :=
  ⟨x, hx⟩

@[simp] theorem coe_integralElement (x : ℚ_[l.value]) (hx : ‖x‖ ≤ 1) :
    (integralElement l x hx : ℚ_[l.value]) = x := rfl

theorem integralElement_norm (x : ℚ_[l.value]) (hx : ‖x‖ ≤ 1) :
    ‖integralElement l x hx‖ = ‖x‖ := by
  exact PadicInt.norm_eq_padic_norm hx

def integralQ : ℤ_[l.value] :=
  integralElement l (q l) (q_norm_lt_one l).le

def integralA4 : ℤ_[l.value] :=
  integralElement l (TateCurve.a4 ℚ_[l.value] (q l))
    (a4_norm_lt_one l).le

def integralA6 : ℤ_[l.value] :=
  integralElement l (TateCurve.a6 ℚ_[l.value] (q l))
    ((a6_norm_eq l).trans_le (q_norm_lt_one l).le)

def integralC4 : ℤ_[l.value] :=
  integralElement l ((canonicalCurve l).c₄)
    (c4_norm_eq_one l).le

def integralOneSubQ : ℤ_[l.value] :=
  integralElement l (1 - q l)
    (le_of_eq (by
      simpa using (denominator_norm_eq_one l (n := 1) (by norm_num))))

theorem coe_integralQ : (integralQ l : ℚ_[l.value]) = q l := by
  rfl

theorem coe_integralA4 :
    (integralA4 l : ℚ_[l.value]) = TateCurve.a4 ℚ_[l.value] (q l) := by
  rfl

theorem coe_integralA6 :
    (integralA6 l : ℚ_[l.value]) = TateCurve.a6 ℚ_[l.value] (q l) := by
  rfl

theorem coe_integralC4 :
    (integralC4 l : ℚ_[l.value]) = (canonicalCurve l).c₄ := by
  rfl

theorem coe_integralOneSubQ :
    (integralOneSubQ l : ℚ_[l.value]) = 1 - q l := by
  rfl

theorem integralQ_norm : ‖integralQ l‖ = ‖q l‖ := by
  exact integralElement_norm l (q l) (q_norm_lt_one l).le

theorem integralA4_norm : ‖integralA4 l‖ =
    ‖TateCurve.a4 ℚ_[l.value] (q l)‖ := by
  exact integralElement_norm l _ (a4_norm_lt_one l).le

theorem integralA6_norm : ‖integralA6 l‖ =
    ‖TateCurve.a6 ℚ_[l.value] (q l)‖ := by
  exact integralElement_norm l _
    ((a6_norm_eq l).trans_le (q_norm_lt_one l).le)

theorem integralC4_norm : ‖integralC4 l‖ = 1 := by
  calc
    ‖integralC4 l‖ = ‖(canonicalCurve l).c₄‖ :=
      integralElement_norm l _ (c4_norm_eq_one l).le
    _ = 1 := c4_norm_eq_one l

theorem integralOneSubQ_norm : ‖integralOneSubQ l‖ = 1 := by
  calc
    ‖integralOneSubQ l‖ = ‖1 - q l‖ :=
      integralElement_norm l _ (le_of_eq (by
        simpa using (denominator_norm_eq_one l (n := 1) (by norm_num))))
    _ = 1 := by
      simpa using (denominator_norm_eq_one l (n := 1) (by norm_num))

theorem integralQ_mem_nonunits : integralQ l ∈ nonunits ℤ_[l.value] := by
  rw [PadicInt.mem_nonunits, integralQ_norm]
  exact q_norm_lt_one l

theorem integralA4_mem_nonunits : integralA4 l ∈ nonunits ℤ_[l.value] := by
  rw [PadicInt.mem_nonunits, integralA4_norm]
  exact a4_norm_lt_one l

theorem integralA6_mem_nonunits : integralA6 l ∈ nonunits ℤ_[l.value] := by
  rw [PadicInt.mem_nonunits, integralA6_norm, a6_norm_eq]
  exact q_norm_lt_one l

theorem integralC4_not_mem_nonunits :
    integralC4 l ∉ nonunits ℤ_[l.value] := by
  intro h
  have hn := PadicInt.mem_nonunits.mp h
  rw [integralC4_norm] at hn
  exact (lt_irrefl (1 : ℝ)) hn

theorem integralC4_isUnit : IsUnit (integralC4 l) := by
  by_contra h
  exact integralC4_not_mem_nonunits l ((mem_nonunits_iff).2 h)

theorem integralOneSubQ_not_mem_nonunits :
    integralOneSubQ l ∉ nonunits ℤ_[l.value] := by
  intro h
  have hn := PadicInt.mem_nonunits.mp h
  rw [integralOneSubQ_norm] at hn
  exact (lt_irrefl (1 : ℝ)) hn

theorem integralOneSubQ_isUnit : IsUnit (integralOneSubQ l) := by
  by_contra h
  exact integralOneSubQ_not_mem_nonunits l ((mem_nonunits_iff).2 h)

def inMaximalIdeal (z : ℤ_[l.value]) : Prop :=
  z ∈ IsLocalRing.maximalIdeal ℤ_[l.value]

theorem inMaximalIdeal_iff_norm_lt_one (z : ℤ_[l.value]) :
    inMaximalIdeal l z ↔ ‖z‖ < 1 := by
  rw [inMaximalIdeal, IsLocalRing.mem_maximalIdeal,
    PadicInt.mem_nonunits]

theorem integralQ_inMaximalIdeal : inMaximalIdeal l (integralQ l) := by
  rw [inMaximalIdeal_iff_norm_lt_one, integralQ_norm]
  exact q_norm_lt_one l

theorem integralA4_inMaximalIdeal : inMaximalIdeal l (integralA4 l) := by
  rw [inMaximalIdeal_iff_norm_lt_one, integralA4_norm]
  exact a4_norm_lt_one l

theorem integralA6_inMaximalIdeal : inMaximalIdeal l (integralA6 l) := by
  rw [inMaximalIdeal_iff_norm_lt_one, integralA6_norm, a6_norm_eq]
  exact q_norm_lt_one l

theorem integralC4_not_inMaximalIdeal :
    ¬ inMaximalIdeal l (integralC4 l) := by
  rw [inMaximalIdeal_iff_norm_lt_one, integralC4_norm]
  norm_num

theorem integralOneSubQ_not_inMaximalIdeal :
    ¬ inMaximalIdeal l (integralOneSubQ l) := by
  rw [inMaximalIdeal_iff_norm_lt_one, integralOneSubQ_norm]
  norm_num

theorem inMaximalIdeal_add {x y : ℤ_[l.value]}
    (hx : inMaximalIdeal l x) (hy : inMaximalIdeal l y) :
    inMaximalIdeal l (x + y) := by
  rw [inMaximalIdeal_iff_norm_lt_one] at hx hy ⊢
  change ‖(x : ℚ_[l.value]) + (y : ℚ_[l.value])‖ < 1
  have h := Padic.nonarchimedean (p := l.value)
    (x : ℚ_[l.value]) (y : ℚ_[l.value])
  have hmax : max ‖(x : ℚ_[l.value])‖ ‖(y : ℚ_[l.value])‖ < 1 :=
    max_lt hx hy
  exact lt_of_le_of_lt (by simpa using h) hmax

theorem inMaximalIdeal_neg {x : ℤ_[l.value]}
    (hx : inMaximalIdeal l x) : inMaximalIdeal l (-x) := by
  rw [inMaximalIdeal_iff_norm_lt_one] at hx ⊢
  simpa using hx

theorem inMaximalIdeal_mul {x y : ℤ_[l.value]}
    (hx : inMaximalIdeal l x) : inMaximalIdeal l (x * y) := by
  rw [inMaximalIdeal_iff_norm_lt_one] at hx ⊢
  have hy : ‖(y : ℚ_[l.value])‖ ≤ 1 := PadicInt.norm_le_one y
  have hmul : ‖(x : ℚ_[l.value]) * (y : ℚ_[l.value])‖ ≤
      ‖(x : ℚ_[l.value])‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hy
  exact lt_of_le_of_lt hmul hx

theorem inMaximalIdeal_smul_nat {x : ℤ_[l.value]} (n : ℕ)
    (hx : inMaximalIdeal l x) : inMaximalIdeal l (n • x) := by
  induction n with
  | zero => simp [inMaximalIdeal_iff_norm_lt_one]
  | succ n ih =>
      rw [add_nsmul]
      exact inMaximalIdeal_add l ih (by simpa using hx)

end IntegralCoefficientWitnesses

section IntegralWeierstrassPresentation

def integralCurve : WeierstrassCurve ℤ_[l.value] :=
  WeierstrassCurve.mk 1 0 0 (integralA4 l) (integralA6 l)

theorem integralCurve_a1 : (integralCurve l).a₁ = 1 := rfl

theorem integralCurve_a2 : (integralCurve l).a₂ = 0 := rfl

theorem integralCurve_a3 : (integralCurve l).a₃ = 0 := rfl

theorem integralCurve_a4 : (integralCurve l).a₄ = integralA4 l := rfl

theorem integralCurve_a6 : (integralCurve l).a₆ = integralA6 l := rfl

def integralCurveMap : WeierstrassCurve ℚ_[l.value] :=
  (integralCurve l).map (algebraMap (ℤ_[l.value]) (ℚ_[l.value]))

theorem integralCurveMap_a1 : (integralCurveMap l).a₁ = 1 := by
  simp [integralCurveMap, integralCurve]

theorem integralCurveMap_a2 : (integralCurveMap l).a₂ = 0 := by
  simp [integralCurveMap, integralCurve]

theorem integralCurveMap_a3 : (integralCurveMap l).a₃ = 0 := by
  simp [integralCurveMap, integralCurve]

theorem integralCurveMap_a4 : (integralCurveMap l).a₄ =
    TateCurve.a4 ℚ_[l.value] (q l) := by
  simp [integralCurveMap, integralCurve, integralA4]

theorem integralCurveMap_a6 : (integralCurveMap l).a₆ =
    TateCurve.a6 ℚ_[l.value] (q l) := by
  simp [integralCurveMap, integralCurve, integralA6]

theorem integralCurveMap_eq_canonical :
    integralCurveMap l = canonicalCurve l := by
  ext <;> simp [integralCurveMap, integralCurve, canonicalCurve,
    integralA4, integralA6]

theorem canonicalCurve_has_integral_presentation :
    ∃ W : WeierstrassCurve ℤ_[l.value],
      W.map (algebraMap (ℤ_[l.value]) (ℚ_[l.value])) = canonicalCurve l :=
  ⟨integralCurve l, integralCurveMap_eq_canonical l⟩

theorem integralPresentation_a4_is_nonunit :
    (integralCurve l).a₄ ∈ nonunits ℤ_[l.value] := by
  rw [integralCurve_a4]
  exact integralA4_mem_nonunits l

theorem integralPresentation_a6_is_nonunit :
    (integralCurve l).a₆ ∈ nonunits ℤ_[l.value] := by
  rw [integralCurve_a6]
  exact integralA6_mem_nonunits l

theorem integralPresentation_c4_is_unit :
    IsUnit (integralCurve l).c₄ := by
  change IsUnit (integralC4 l)
  exact integralC4_isUnit l

theorem integralPresentation_one_sub_q_is_unit :
    IsUnit (integralOneSubQ l) := integralOneSubQ_isUnit l

theorem integralPresentation_q_is_nonunit :
    integralQ l ∈ nonunits ℤ_[l.value] := integralQ_mem_nonunits l

end IntegralWeierstrassPresentation

section WeightedLambertCombination

def weightedSeries : ℚ_[l.value] :=
  (5 : ℚ_[l.value]) * series l 3 +
    (7 : ℚ_[l.value]) * series l 5

def weightedPrincipal : ℚ_[l.value] :=
  (12 : ℚ_[l.value]) * principal l 3

def weightedTail : ℚ_[l.value] :=
  (5 : ℚ_[l.value]) * tail l 3 +
    (7 : ℚ_[l.value]) * tail l 5

theorem weightedSeries_eq_a6_numerator :
    weightedSeries l =
      -(12 : ℚ_[l.value]) * TateCurve.a6 ℚ_[l.value] (q l) := by
  rw [weightedSeries, a6_series_identity]
  field_simp

theorem weightedSeries_decomposition :
    weightedSeries l = weightedPrincipal l + weightedTail l := by
  rw [weightedSeries, weightedPrincipal, weightedTail,
    coefficient_series_decomposition l 3,
    coefficient_series_decomposition l 5]
  simp [principal_eq]
  ring

theorem weightedPrincipal_eq :
    weightedPrincipal l = (12 : ℚ_[l.value]) * (q l / (1 - q l)) := by
  simp [weightedPrincipal, principal_eq]

theorem weightedPrincipal_norm : ‖weightedPrincipal l‖ = ‖q l‖ := by
  rw [weightedPrincipal_eq, norm_mul, norm_twelve_eq_one, one_mul,
    norm_div]
  have hd : ‖1 - q l‖ = 1 := by
    simpa using (denominator_norm_eq_one l (n := 1) (by norm_num))
  rw [hd, div_one]

theorem weightedPrincipal_ne_zero : weightedPrincipal l ≠ 0 := by
  intro h
  have hn := congrArg norm h
  rw [weightedPrincipal_norm, norm_zero] at hn
  exact (ne_of_gt (q_norm_pos l)) hn

theorem weightedTail_norm_le :
    ‖weightedTail l‖ ≤ ‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹ := by
  have h3 : ‖(5 : ℚ_[l.value]) * tail l 3‖ ≤
      ‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg (tail l 3))
      (norm_five_le_one l)).trans (tail_norm_le_closed l 3)
  have h5 : ‖(7 : ℚ_[l.value]) * tail l 5‖ ≤
      ‖q l‖ ^ 2 * (1 - ‖q l‖)⁻¹ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg (tail l 5))
      (norm_seven_le_one l)).trans (tail_norm_le_closed l 5)
  have hsum := Padic.nonarchimedean (p := l.value)
    ((5 : ℚ_[l.value]) * tail l 3)
    ((7 : ℚ_[l.value]) * tail l 5)
  exact hsum.trans (max_le h3 h5)

theorem weightedTail_norm_lt : ‖weightedTail l‖ < ‖q l‖ := by
  exact (weightedTail_norm_le l).trans_lt (by
    rw [← div_eq_mul_inv]
    apply (div_lt_iff₀ (sub_pos.mpr (q_norm_lt_one l))).2
    nlinarith [q_norm_pos l, q_norm_lt_half l])

theorem weightedSeries_norm_eq : ‖weightedSeries l‖ = ‖q l‖ := by
  rw [weightedSeries_decomposition l]
  have hne : ‖weightedPrincipal l‖ ≠ ‖weightedTail l‖ :=
    by simpa [weightedPrincipal_norm l] using
      (ne_of_gt (weightedTail_norm_lt l))
  rw [Padic.add_eq_max_of_ne hne,
    weightedPrincipal_norm,
    max_eq_left (le_of_lt (weightedTail_norm_lt l))]

theorem weightedSeries_ne_zero : weightedSeries l ≠ 0 := by
  intro h
  have hn := weightedSeries_norm_eq l
  rw [h, norm_zero] at hn
  exact (ne_of_gt (q_norm_pos l)) hn.symm

theorem weightedTail_is_difference :
    weightedSeries l - weightedPrincipal l = weightedTail l := by
  rw [weightedSeries_decomposition l]
  ring

theorem weightedPrincipal_is_strict_approximation :
    ‖weightedSeries l - weightedPrincipal l‖ <
      ‖weightedPrincipal l‖ := by
  rw [weightedTail_is_difference l, weightedPrincipal_norm]
  exact weightedTail_norm_lt l

theorem weightedSeries_norm_is_principal_norm :
    ‖weightedSeries l‖ = ‖weightedPrincipal l‖ := by
  rw [weightedSeries_norm_eq, weightedPrincipal_norm]

theorem weightedSeries_is_not_zero : weightedSeries l ≠ 0 :=
  weightedSeries_ne_zero l

theorem weightedSeries_is_not_principal_iff :
    weightedSeries l = weightedPrincipal l ↔ weightedTail l = 0 := by
  constructor
  · intro h
    have h' : weightedSeries l - weightedPrincipal l = 0 :=
      sub_eq_zero.mpr h
    rw [weightedTail_is_difference l] at h'
    exact h'
  · intro h
    have hd : weightedSeries l - weightedPrincipal l = 0 := by
      simpa [weightedTail_is_difference l] using h
    exact sub_eq_zero.mp hd

theorem weightedSeries_has_positive_norm : 0 < ‖weightedSeries l‖ := by
  rw [weightedSeries_norm_eq]
  exact q_norm_pos l

theorem weightedTail_has_nonnegative_norm : 0 ≤ ‖weightedTail l‖ :=
  norm_nonneg _

theorem weightedTail_is_strictly_contractive : ‖weightedTail l‖ < 1 :=
  (weightedTail_norm_lt l).trans (q_norm_lt_one l)

theorem a6_is_negative_weightedSeries_division :
    TateCurve.a6 ℚ_[l.value] (q l) =
      -weightedSeries l / 12 := by
  rw [weightedSeries, a6_series_identity]

theorem a6_principal_is_negative_weightedPrincipal_division :
    a6Principal l = -weightedPrincipal l / 12 := by
  rw [weightedPrincipal_eq, a6Principal]
  field_simp

theorem a6_remainder_is_negative_weightedTail_division :
    a6Remainder l = -weightedTail l / 12 := by
  rw [a6Remainder, weightedTail]

theorem a6_decomposition_from_weighted_series :
    TateCurve.a6 ℚ_[l.value] (q l) =
      -weightedPrincipal l / 12 - weightedTail l / 12 := by
  rw [a6_is_negative_weightedSeries_division,
    weightedSeries_decomposition l]
  ring

theorem weighted_series_remainder_norm_lt_divisor :
    ‖weightedTail l / 12‖ < ‖weightedPrincipal l / 12‖ := by
  rw [norm_div, norm_div, norm_twelve_eq_one]
  simp only [div_one]
  rw [weightedPrincipal_norm]
  exact weightedTail_norm_lt l

theorem weighted_series_divisor_is_unit :
    IsUnit (12 : ℤ_[l.value]) := by
  have h : (12 : ℤ_[l.value]) ∉ nonunits ℤ_[l.value] := by
    intro hn
    have hnorm := PadicInt.mem_nonunits.mp hn
    have hq : ‖(12 : ℚ_[l.value])‖ = 1 := norm_twelve_eq_one l
    change ‖(12 : ℚ_[l.value])‖ < 1 at hnorm
    rw [hq] at hnorm
    norm_num at hnorm
  by_contra hunit
  exact h ((mem_nonunits_iff).2 hunit)

theorem weighted_series_divisor_norm :
    ‖(12 : ℤ_[l.value])‖ = 1 := by
  change ‖(12 : ℚ_[l.value])‖ = 1
  exact norm_twelve_eq_one l

theorem weighted_series_combination_is_nonzero :
    5 * series l 3 + 7 * series l 5 ≠ 0 := by
  simpa [weightedSeries] using weightedSeries_ne_zero l

theorem a6_nonzero_from_weighted_series :
    TateCurve.a6 ℚ_[l.value] (q l) ≠ 0 := by
  exact a6_ne_zero l

theorem a6_norm_from_weighted_series :
    ‖TateCurve.a6 ℚ_[l.value] (q l)‖ =
      ‖weightedSeries l‖ / ‖(12 : ℚ_[l.value])‖ := by
  rw [a6_is_negative_weightedSeries_division, norm_div,
    norm_neg]

theorem a6_norm_reduced :
    ‖TateCurve.a6 ℚ_[l.value] (q l)‖ = ‖q l‖ := by
  exact a6_norm_eq l

theorem a6_norm_reduced_from_weighted_norm :
    ‖TateCurve.a6 ℚ_[l.value] (q l)‖ = ‖weightedSeries l‖ := by
  rw [a6_norm_from_weighted_series, norm_twelve_eq_one, div_one]

theorem weighted_principal_tail_certificate :
    ‖weightedTail l‖ < ‖weightedPrincipal l‖ ∧
      ‖weightedSeries l‖ = ‖weightedPrincipal l‖ :=
  ⟨by rw [weightedPrincipal_norm]; exact weightedTail_norm_lt l,
    weightedSeries_norm_is_principal_norm l⟩

end WeightedLambertCombination

section LocalReductionBoundary

def localCoefficientPacket : Prop :=
  ∃ qI a4I a6I c4I : ℤ_[l.value],
    (qI : ℚ_[l.value]) = q l ∧
    (a4I : ℚ_[l.value]) = TateCurve.a4 ℚ_[l.value] (q l) ∧
    (a6I : ℚ_[l.value]) = TateCurve.a6 ℚ_[l.value] (q l) ∧
    (c4I : ℚ_[l.value]) = (canonicalCurve l).c₄ ∧
    qI ∈ nonunits ℤ_[l.value] ∧
    a4I ∈ nonunits ℤ_[l.value] ∧
    a6I ∈ nonunits ℤ_[l.value] ∧
    IsUnit c4I

theorem localCoefficientPacket_exists : localCoefficientPacket l := by
  refine ⟨integralQ l, integralA4 l, integralA6 l, integralC4 l, ?_⟩
  refine ⟨coe_integralQ l, coe_integralA4 l, coe_integralA6 l,
    coe_integralC4 l, integralQ_mem_nonunits l, integralA4_mem_nonunits l,
    integralA6_mem_nonunits l, integralC4_isUnit l⟩

theorem localCoefficientPacket_has_q_parameter :
    localCoefficientPacket l →
      ∃ qI : ℤ_[l.value], (qI : ℚ_[l.value]) = q l := by
  rintro ⟨qI, _, _, _, hq, _, _, _, _, _, _, _⟩
  exact ⟨qI, hq⟩

theorem localCoefficientPacket_has_nonunit_a4 :
    localCoefficientPacket l →
      ∃ a4I : ℤ_[l.value],
        (a4I : ℚ_[l.value]) = TateCurve.a4 ℚ_[l.value] (q l) ∧
          a4I ∈ nonunits ℤ_[l.value] := by
  rintro ⟨qI, a4I, a6I, c4I, hq, ha4, ha6, hc4,
    hqnu, ha4nu, ha6nu, hc4u⟩
  exact ⟨a4I, ha4, ha4nu⟩

theorem localCoefficientPacket_has_nonunit_a6 :
    localCoefficientPacket l →
      ∃ a6I : ℤ_[l.value],
        (a6I : ℚ_[l.value]) = TateCurve.a6 ℚ_[l.value] (q l) ∧
          a6I ∈ nonunits ℤ_[l.value] := by
  rintro ⟨qI, a4I, a6I, c4I, hq, ha4, ha6, hc4,
    hqnu, ha4nu, ha6nu, hc4u⟩
  exact ⟨a6I, ha6, ha6nu⟩

theorem localCoefficientPacket_has_unit_c4 :
    localCoefficientPacket l →
      ∃ c4I : ℤ_[l.value],
        (c4I : ℚ_[l.value]) = (canonicalCurve l).c₄ ∧ IsUnit c4I := by
  rintro ⟨qI, a4I, a6I, c4I, hq, ha4, ha6, hc4,
    hqnu, ha4nu, ha6nu, hc4u⟩
  exact ⟨c4I, hc4, hc4u⟩

def discriminantNonzeroObligation : Prop :=
  (canonicalCurve l).Δ ≠ 0

theorem discriminantNonzeroObligation_iff_elliptic :
    discriminantNonzeroObligation l ↔ (canonicalCurve l).IsElliptic := by
  exact canonicalCurve_is_elliptic_iff_delta_ne_zero l |>.symm

theorem discriminantNonzeroObligation_iff_series :
    discriminantNonzeroObligation l ↔
      (TateCurve.a4 ℚ_[l.value] (q l)) ^ 2 -
        TateCurve.a6 ℚ_[l.value] (q l) -
        64 * (TateCurve.a4 ℚ_[l.value] (q l)) ^ 3 -
        432 * (TateCurve.a6 ℚ_[l.value] (q l)) ^ 2 +
        72 * TateCurve.a4 ℚ_[l.value] (q l) *
          TateCurve.a6 ℚ_[l.value] (q l) ≠ 0 := by
  exact canonicalCurve_delta_ne_zero_iff_series l

theorem localPacket_does_not_prove_discriminant :
    localCoefficientPacket l ∧
      discriminantNonzeroObligation l ↔
      discriminantNonzeroObligation l := by
  constructor
  · rintro ⟨_, hΔ⟩
    exact hΔ
  · intro hΔ
    exact ⟨localCoefficientPacket_exists l, hΔ⟩

theorem localPacket_is_independent_of_delta_obligation :
    localCoefficientPacket l := localCoefficientPacket_exists l

theorem localPacket_c4_is_not_a_delta_certificate :
    localCoefficientPacket l →
      IsUnit (integralC4 l) := by
  intro _
  exact integralC4_isUnit l

theorem localPacket_q_is_strictly_contracting :
    localCoefficientPacket l → ‖q l‖ < 1 := by
  intro _
  exact q_norm_lt_one l

theorem localPacket_series_are_summable :
    localCoefficientPacket l →
      Summable (fun n : ℕ => term l 3 n) ∧
        Summable (fun n : ℕ => term l 5 n) := by
  intro _
  exact ⟨term_summable l 3, term_summable l 5⟩

theorem localPacket_has_integral_presentation :
    localCoefficientPacket l →
      ∃ W : WeierstrassCurve ℤ_[l.value],
        W.map (algebraMap (ℤ_[l.value]) (ℚ_[l.value])) = canonicalCurve l := by
  intro _
  exact canonicalCurve_has_integral_presentation l

theorem localPacket_elliptic_extension_iff :
    (∃ _hΔ : discriminantNonzeroObligation l,
      localCoefficientPacket l ∧ (canonicalCurve l).IsElliptic) ↔
      discriminantNonzeroObligation l := by
  constructor
  · rintro ⟨hΔ, _, _⟩
    exact hΔ
  · intro hΔ
    exact ⟨hΔ, localCoefficientPacket_exists l,
      (canonicalCurve_is_elliptic_iff_delta_ne_zero l).mpr hΔ⟩

end LocalReductionBoundary

section IntegralPowersAndDenominators

def integralQPower (n : ℕ) : ℤ_[l.value] := (integralQ l) ^ n

@[simp] theorem coe_integralQPower (n : ℕ) :
    (integralQPower l n : ℚ_[l.value]) = q l ^ n := by
  simp [integralQPower, coe_integralQ]

theorem integralQPower_norm (n : ℕ) :
    ‖integralQPower l n‖ = ‖q l‖ ^ n := by
  change ‖(integralQPower l n : ℚ_[l.value])‖ = ‖q l‖ ^ n
  rw [coe_integralQPower, norm_pow]

theorem integralQPower_zero : integralQPower l 0 = 1 := by
  simp [integralQPower]

theorem integralQPower_succ (n : ℕ) :
    integralQPower l (n + 1) = integralQPower l n * integralQ l := by
  simp [integralQPower, pow_succ, mul_comm]

theorem integralQPower_ne_zero (n : ℕ) : integralQPower l n ≠ 0 := by
  intro h
  have hc := congrArg (fun z : ℤ_[l.value] =>
    (z : ℚ_[l.value])) h
  have hpow : q l ^ n = (0 : ℚ_[l.value]) := by
    simpa [coe_integralQPower] using hc
  exact (pow_ne_zero n (q_ne_zero l)) hpow

theorem integralQPower_inMaximalIdeal {n : ℕ} (hn : 0 < n) :
    inMaximalIdeal l (integralQPower l n) := by
  rw [inMaximalIdeal_iff_norm_lt_one, integralQPower_norm]
  rw [← q_power_norm_eq l n]
  exact q_power_norm_lt_one l hn

theorem integralQPower_mem_nonunits {n : ℕ} (hn : 0 < n) :
    integralQPower l n ∈ nonunits ℤ_[l.value] := by
  rw [PadicInt.mem_nonunits]
  rw [integralQPower_norm]
  rw [← q_power_norm_eq l n]
  exact q_power_norm_lt_one l hn

def integralDenominator (n : ℕ) : ℤ_[l.value] :=
  1 - integralQPower l n

@[simp] theorem coe_integralDenominator {n : ℕ} (_hn : 0 < n) :
    (integralDenominator l n : ℚ_[l.value]) = 1 - q l ^ n := by
  simp [integralDenominator, coe_integralQPower]

theorem integralDenominator_norm {n : ℕ} (hn : 0 < n) :
    ‖integralDenominator l n‖ = 1 := by
  change ‖(integralDenominator l n : ℚ_[l.value])‖ = 1
  rw [coe_integralDenominator l hn, denominator_norm_eq_one l hn]

theorem integralDenominator_isUnit {n : ℕ} (hn : 0 < n) :
    IsUnit (integralDenominator l n) := by
  by_contra h
  have hnon : integralDenominator l n ∈ nonunits ℤ_[l.value] :=
    (mem_nonunits_iff).2 h
  have hnorm := PadicInt.mem_nonunits.mp hnon
  rw [integralDenominator_norm l hn] at hnorm
  norm_num at hnorm

theorem integralDenominator_not_inMaximalIdeal {n : ℕ} (hn : 0 < n) :
    ¬ inMaximalIdeal l (integralDenominator l n) := by
  rw [inMaximalIdeal_iff_norm_lt_one, integralDenominator_norm l hn]
  norm_num

def integralTerm (weight n : ℕ) : ℤ_[l.value] :=
  integralElement l (term l weight n) (term_is_integral_norm l weight n)

theorem integralTerm_norm (weight n : ℕ) :
    ‖integralTerm l weight n‖ = ‖term l weight n‖ := by
  exact integralElement_norm l _ (term_is_integral_norm l weight n)

theorem integralTerm_eq_previous (weight n : ℕ) :
    integralTerm l weight n =
      integralElement l (term l weight n) (term_is_integral_norm l weight n) := rfl

theorem integralTerm_coe_eq_term (weight n : ℕ) :
    (integralTerm l weight n : ℚ_[l.value]) = term l weight n := rfl

theorem integralTerm_coe_norm (weight n : ℕ) :
    ‖(integralTerm l weight n : ℚ_[l.value])‖ = ‖term l weight n‖ := by
  rw [integralTerm_coe_eq_term]

theorem integralTerm_has_denominator (_weight n : ℕ) :
    n = 0 ∨ ∃ d : ℤ_[l.value],
      (d : ℚ_[l.value]) = 1 - q l ^ n ∧ IsUnit d := by
  by_cases hn : 0 < n
  · exact Or.inr ⟨integralDenominator l n,
      coe_integralDenominator l hn, integralDenominator_isUnit l hn⟩
  · exact Or.inl (Nat.eq_zero_of_not_pos hn)

theorem integralTerm_positive_is_nonunit {weight n : ℕ} (hn : 0 < n) :
    integralTerm l weight n ∈ nonunits ℤ_[l.value] := by
  rw [PadicInt.mem_nonunits]
  have hnorm : ‖integralTerm l weight n‖ = ‖term l weight n‖ :=
    integralTerm_norm l weight n
  rw [hnorm]
  exact term_norm_lt_one l weight n hn

theorem integralTerm_positive_inMaximalIdeal {weight n : ℕ}
    (hn : 0 < n) : inMaximalIdeal l (integralTerm l weight n) := by
  rw [inMaximalIdeal_iff_norm_lt_one, integralTerm_norm]
  exact term_norm_lt_one l weight n hn

theorem integralTerm_one_has_same_norm_as_q (weight : ℕ) :
    ‖integralTerm l weight 1‖ = ‖q l‖ := by
  rw [integralTerm_norm, term_norm_eq_q_power_one]

theorem integralTerm_two_has_smaller_norm (weight : ℕ) :
    ‖integralTerm l weight 2‖ < ‖q l‖ := by
  rw [integralTerm_norm]
  exact term_norm_lt_first l (by norm_num)

theorem integralTerm_tail_is_a_strict_perturbation (weight : ℕ) :
    ‖tail l weight‖ < ‖(integralTerm l weight 1 : ℚ_[l.value])‖ := by
  rw [integralTerm_coe_norm, term_norm_eq_q_power_one]
  exact tail_norm_lt_first l weight

theorem integralDenominator_is_not_zero {n : ℕ} (hn : 0 < n) :
    integralDenominator l n ≠ 0 := by
  intro h
  have hc := congrArg (fun z : ℤ_[l.value] =>
    (z : ℚ_[l.value])) h
  rw [coe_integralDenominator l hn] at hc
  exact denominator_ne_zero l hn hc

theorem integralQPower_plus_denominator (n : ℕ) :
    integralQPower l n + integralDenominator l n = 1 := by
  simp [integralDenominator]

theorem integralQPower_mul_integralDenominator_relation {n : ℕ}
    (_hn : 0 < n) :
    integralQPower l n * integralDenominator l n =
      integralQPower l n - integralQPower l n ^ 2 := by
  rw [integralDenominator]
  ring

theorem integralDenominator_unit_preserves_term_definition {weight n : ℕ}
    (hn : 0 < n) :
    (term l weight n : ℚ_[l.value]) *
        (integralDenominator l n : ℚ_[l.value]) =
      (n : ℚ_[l.value]) ^ weight * q l ^ n := by
  rw [term_eq_of_pos l hn,
    coe_integralDenominator l hn]
  rw [div_mul_cancel₀ _ (denominator_ne_zero l hn)]

end IntegralPowersAndDenominators

section FiniteLevelPackets

def finiteTermPacket (weight N : ℕ) : Fin N → ℚ_[l.value] :=
  fun i => term l weight i.1

def finiteTermNormPacket (weight N : ℕ) : Fin N → ℝ :=
  fun i => ‖finiteTermPacket l weight N i‖

theorem finiteTermPacket_apply (weight N : ℕ) (i : Fin N) :
    finiteTermPacket l weight N i = term l weight i.1 := rfl

theorem finiteTermNormPacket_apply (weight N : ℕ) (i : Fin N) :
    finiteTermNormPacket l weight N i = ‖term l weight i.1‖ := rfl

theorem finiteTermPacket_norm_le_geometric (weight N : ℕ) (i : Fin N) :
    ‖finiteTermPacket l weight N i‖ ≤ ‖q l‖ ^ i.1 := by
  exact term_norm_le_geometric l i.1 weight

theorem finiteTermPacket_zero (weight : ℕ) (i : Fin 0) :
    finiteTermPacket l weight 0 i = 0 := by
  exact Fin.elim0 i

theorem finiteTermPacket_first (_weight : ℕ) (i : Fin 1) :
    finiteTermPacket l _weight 1 i = 0 := by
  simp [finiteTermPacket, term_zero]

theorem finiteTermPacket_second (_weight : ℕ) (i : Fin 2) :
    i.1 = 0 ∨ i.1 = 1 := by
  omega

theorem finiteTermPacket_second_values (weight : ℕ) (i : Fin 2) :
    finiteTermPacket l weight 2 i =
      if i.1 = 0 then 0 else principal l weight := by
  rcases finiteTermPacket_second weight i with hi | hi
  · simp [finiteTermPacket, hi, term_zero]
  · have hi' : i.1 = 1 := hi
    simp [finiteTermPacket, hi', principal, term_one]

theorem finiteTermPacket_sum (weight N : ℕ) :
    ∑ i : Fin N, finiteTermPacket l weight N i = partialSum l weight N := by
  rw [partialSum, ← Fin.sum_univ_eq_sum_range]
  rfl

theorem finiteTermPacket_sum_norm_le (weight N : ℕ) :
    ‖∑ i : Fin N, finiteTermPacket l weight N i‖ ≤
      ∑ i : Fin N, ‖q l‖ ^ i.1 := by
  calc
    ‖∑ i : Fin N, finiteTermPacket l weight N i‖ ≤
        ∑ i : Fin N, ‖finiteTermPacket l weight N i‖ :=
      norm_sum_le Finset.univ _
    _ ≤ ∑ i : Fin N, ‖q l‖ ^ i.1 := by
      exact Finset.sum_le_sum fun i hi =>
        term_norm_le_geometric l i.1 weight

theorem finiteTermPacket_tail_sum (weight N : ℕ) :
    series l weight - ∑ i : Fin N, finiteTermPacket l weight N i =
      shiftedTail l weight N := by
  rw [finiteTermPacket_sum, series_eq_partialSum_add_shiftedTail]
  ring

theorem finiteTermPacket_error_norm_le (weight N : ℕ) :
    ‖series l weight - ∑ i : Fin N, finiteTermPacket l weight N i‖ ≤
      ‖q l‖ ^ N * (1 - ‖q l‖)⁻¹ := by
  rw [finiteTermPacket_tail_sum]
  exact shiftedTail_norm_le_closed l weight N

theorem finiteTermPacket_error_is_geometrically_bounded (weight N : ℕ) :
    ‖series l weight -
        ∑ i : Fin N, finiteTermPacket l weight N i‖ ≤
      ‖q l‖ ^ N * (1 - ‖q l‖)⁻¹ :=
  finiteTermPacket_error_norm_le l weight N

theorem finiteTermPacket_two_sum_is_principal (weight : ℕ) :
    ∑ i : Fin 2, finiteTermPacket l weight 2 i = principal l weight := by
  rw [finiteTermPacket_sum, finite_first_two_exact]

theorem finiteTermPacket_two_error_is_tail (weight : ℕ) :
    series l weight - ∑ i : Fin 2, finiteTermPacket l weight 2 i =
      tail l weight := by
  rw [finiteTermPacket_sum, finite_first_two_exact]
  exact series_minus_principal_is_tail l weight

theorem finiteTermPacket_two_error_is_strict (weight : ℕ) :
    ‖series l weight - ∑ i : Fin 2, finiteTermPacket l weight 2 i‖ <
      ‖q l‖ := by
  rw [finiteTermPacket_two_error_is_tail]
  exact tail_norm_lt_first l weight

theorem finiteTermPacket_three_sum (weight : ℕ) :
    ∑ i : Fin 3, finiteTermPacket l weight 3 i =
      principal l weight + term l weight 2 := by
  rw [finiteTermPacket_sum, partialSum_three]
  simp [principal]

theorem finiteTermPacket_three_error_norm_le (weight : ℕ) :
    ‖series l weight - ∑ i : Fin 3, finiteTermPacket l weight 3 i‖ ≤
      ‖q l‖ ^ 3 * (1 - ‖q l‖)⁻¹ := by
  rw [finiteTermPacket_sum]
  exact partialSum_error_norm_le l weight 3

end FiniteLevelPackets

section FirstTailCertificates

structure FirstTailCertificate (weight : ℕ) where
  first : ℚ_[l.value]
  tailValue : ℚ_[l.value]
  decomposition : series l weight = first + tailValue
  first_eq_principal : first = principal l weight
  tail_eq_tail : tailValue = tail l weight
  first_norm : ‖first‖ = ‖q l‖
  tail_norm_lt : ‖tailValue‖ < ‖q l‖

def firstTailCertificate (weight : ℕ) : FirstTailCertificate l weight :=
  { first := principal l weight
    tailValue := tail l weight
    decomposition := series_eq_first_plus_tail l weight
    first_eq_principal := rfl
    tail_eq_tail := rfl
    first_norm := principal_norm l weight
    tail_norm_lt := tail_norm_lt_first l weight }

theorem firstTailCertificate_first (weight : ℕ) :
    (firstTailCertificate l weight).first = principal l weight := rfl

theorem firstTailCertificate_tail (weight : ℕ) :
    (firstTailCertificate l weight).tailValue = tail l weight := rfl

theorem firstTailCertificate_decomposition (weight : ℕ) :
    series l weight =
      (firstTailCertificate l weight).first +
        (firstTailCertificate l weight).tailValue :=
  (firstTailCertificate l weight).decomposition

theorem firstTailCertificate_first_norm (weight : ℕ) :
    ‖(firstTailCertificate l weight).first‖ = ‖q l‖ :=
  (firstTailCertificate l weight).first_norm

theorem firstTailCertificate_tail_norm_lt (weight : ℕ) :
    ‖(firstTailCertificate l weight).tailValue‖ < ‖q l‖ :=
  (firstTailCertificate l weight).tail_norm_lt

theorem firstTailCertificate_series_norm (weight : ℕ) :
    ‖series l weight‖ = ‖(firstTailCertificate l weight).first‖ := by
  rw [series_norm_eq_first, firstTailCertificate_first_norm]

theorem firstTailCertificate_series_nonzero (weight : ℕ) :
    series l weight ≠ 0 := series_ne_zero l weight

theorem firstTailCertificate_tail_is_small (weight : ℕ) :
    ‖(firstTailCertificate l weight).tailValue‖ <
      ‖(firstTailCertificate l weight).first‖ := by
  rw [firstTailCertificate_first_norm]
  exact firstTailCertificate_tail_norm_lt l weight

theorem firstTailCertificate_unique_first_norm (weight : ℕ)
    (c : FirstTailCertificate l weight) :
    ‖c.first‖ = ‖q l‖ := c.first_norm

theorem firstTailCertificate_unique_tail_bound (weight : ℕ)
    (c : FirstTailCertificate l weight) : ‖c.tailValue‖ < ‖q l‖ :=
  c.tail_norm_lt

theorem firstTailCertificate_has_nonzero_first (weight : ℕ) :
    (firstTailCertificate l weight).first ≠ 0 := by
  intro h
  have hn := firstTailCertificate_first_norm l weight
  rw [h, norm_zero] at hn
  exact (ne_of_gt (q_norm_pos l)) hn.symm

theorem firstTailCertificate_has_strict_perturbation (weight : ℕ) :
    ‖(firstTailCertificate l weight).tailValue‖ <
      ‖(firstTailCertificate l weight).first‖ :=
  firstTailCertificate_tail_is_small l weight

theorem firstTailCertificate_is_a_nonarchimedean_dominance_certificate
    (weight : ℕ) :
    ‖series l weight‖ = ‖(firstTailCertificate l weight).first‖ ∧
      ‖(firstTailCertificate l weight).tailValue‖ <
        ‖(firstTailCertificate l weight).first‖ :=
  ⟨firstTailCertificate_series_norm l weight,
    firstTailCertificate_tail_is_small l weight⟩

end FirstTailCertificates

section CanonicalCoefficientCertificates

structure CanonicalCoefficientCertificate where
  a4 : ℚ_[l.value]
  a6 : ℚ_[l.value]
  c4 : ℚ_[l.value]
  a4_eq : a4 = TateCurve.a4 ℚ_[l.value] (q l)
  a6_eq : a6 = TateCurve.a6 ℚ_[l.value] (q l)
  c4_eq : c4 = (canonicalCurve l).c₄
  a4_norm : ‖a4‖ = ‖(5 : ℚ_[l.value])‖ * ‖q l‖
  a6_norm : ‖a6‖ = ‖q l‖
  c4_norm : ‖c4‖ = 1
  a4_ne_zero : a4 ≠ 0
  a6_ne_zero : a6 ≠ 0
  c4_ne_zero : c4 ≠ 0

def canonicalCoefficientCertificate : CanonicalCoefficientCertificate l :=
  { a4 := TateCurve.a4 ℚ_[l.value] (q l)
    a6 := TateCurve.a6 ℚ_[l.value] (q l)
    c4 := (canonicalCurve l).c₄
    a4_eq := rfl
    a6_eq := rfl
    c4_eq := rfl
    a4_norm := a4_norm_eq l
    a6_norm := a6_norm_eq l
    c4_norm := c4_norm_eq_one l
    a4_ne_zero := a4_ne_zero l
    a6_ne_zero := a6_ne_zero l
    c4_ne_zero := c4_ne_zero l }

theorem canonicalCoefficientCertificate_a4_eq :
    (canonicalCoefficientCertificate l).a4 =
      TateCurve.a4 ℚ_[l.value] (q l) := rfl

theorem canonicalCoefficientCertificate_a6_eq :
    (canonicalCoefficientCertificate l).a6 =
      TateCurve.a6 ℚ_[l.value] (q l) := rfl

theorem canonicalCoefficientCertificate_c4_eq :
    (canonicalCoefficientCertificate l).c4 = (canonicalCurve l).c₄ := rfl

theorem canonicalCoefficientCertificate_a4_norm :
    ‖(canonicalCoefficientCertificate l).a4‖ =
      ‖(5 : ℚ_[l.value])‖ * ‖q l‖ :=
  (canonicalCoefficientCertificate l).a4_norm

theorem canonicalCoefficientCertificate_a6_norm :
    ‖(canonicalCoefficientCertificate l).a6‖ = ‖q l‖ :=
  (canonicalCoefficientCertificate l).a6_norm

theorem canonicalCoefficientCertificate_c4_norm :
    ‖(canonicalCoefficientCertificate l).c4‖ = 1 :=
  (canonicalCoefficientCertificate l).c4_norm

theorem canonicalCoefficientCertificate_a4_nonzero :
    (canonicalCoefficientCertificate l).a4 ≠ 0 :=
  (canonicalCoefficientCertificate l).a4_ne_zero

theorem canonicalCoefficientCertificate_a6_nonzero :
    (canonicalCoefficientCertificate l).a6 ≠ 0 :=
  (canonicalCoefficientCertificate l).a6_ne_zero

theorem canonicalCoefficientCertificate_c4_nonzero :
    (canonicalCoefficientCertificate l).c4 ≠ 0 :=
  (canonicalCoefficientCertificate l).c4_ne_zero

theorem canonicalCoefficientCertificate_a4_integral :
    ‖(canonicalCoefficientCertificate l).a4‖ ≤ 1 := by
  rw [canonicalCoefficientCertificate_a4_norm]
  have h := (a4_norm_lt_one l).le
  rw [a4_norm_eq l] at h
  exact h

theorem canonicalCoefficientCertificate_a6_integral :
    ‖(canonicalCoefficientCertificate l).a6‖ ≤ 1 := by
  rw [canonicalCoefficientCertificate_a6_norm]
  exact (q_norm_lt_one l).le

theorem canonicalCoefficientCertificate_c4_is_unit :
    IsUnit (canonicalCoefficientCertificate l).c4 := by
  rw [canonicalCoefficientCertificate_c4_eq]
  exact c4_is_unit l

theorem canonicalCoefficientCertificate_has_integral_a4 :
    ∃ a4I : ℤ_[l.value],
      (a4I : ℚ_[l.value]) = (canonicalCoefficientCertificate l).a4 := by
  refine ⟨integralA4 l, ?_⟩
  simpa [canonicalCoefficientCertificate_a4_eq] using coe_integralA4 l

theorem canonicalCoefficientCertificate_has_integral_a6 :
    ∃ a6I : ℤ_[l.value],
      (a6I : ℚ_[l.value]) = (canonicalCoefficientCertificate l).a6 := by
  refine ⟨integralA6 l, ?_⟩
  simpa [canonicalCoefficientCertificate_a6_eq] using coe_integralA6 l

theorem canonicalCoefficientCertificate_has_integral_c4 :
    ∃ c4I : ℤ_[l.value],
      (c4I : ℚ_[l.value]) = (canonicalCoefficientCertificate l).c4 := by
  refine ⟨integralC4 l, ?_⟩
  simpa [canonicalCoefficientCertificate_c4_eq] using coe_integralC4 l

theorem canonicalCoefficientCertificate_is_exactly_canonical :
    (canonicalCoefficientCertificate l).a4 =
        TateCurve.a4 ℚ_[l.value] (q l) ∧
      (canonicalCoefficientCertificate l).a6 =
        TateCurve.a6 ℚ_[l.value] (q l) ∧
      (canonicalCoefficientCertificate l).c4 = (canonicalCurve l).c₄ :=
  ⟨rfl, rfl, rfl⟩

end CanonicalCoefficientCertificates

section CanonicalQSeriesAuditPacket

structure CanonicalQSeriesAuditPacket where
  q_value : ℚ_[l.value]
  q_eq_prime : q_value = (l.value : ℚ_[l.value])
  q_contracts : ‖q_value‖ < 1
  denominator_units : ∀ {n : ℕ}, 0 < n → IsUnit (1 - q_value ^ n)
  series_summable : ∀ weight : ℕ,
    Summable (fun n : ℕ => term l weight n)
  principal_norm : ∀ weight : ℕ, ‖principal l weight‖ = ‖q_value‖
  tail_dominance : ∀ weight : ℕ, ‖tail l weight‖ < ‖q_value‖
  coefficient_certificate : CanonicalCoefficientCertificate l

def canonicalQSeriesAuditPacket : CanonicalQSeriesAuditPacket l :=
  { q_value := q l
    q_eq_prime := q_eq_prime l
    q_contracts := q_norm_lt_one l
    denominator_units := fun hn => denominator_is_unit l hn
    series_summable := fun weight => term_summable l weight
    principal_norm := fun weight => principal_norm l weight
    tail_dominance := fun weight => tail_norm_lt_first l weight
    coefficient_certificate := canonicalCoefficientCertificate l }

theorem canonicalQSeriesAuditPacket_q_value :
    (canonicalQSeriesAuditPacket l).q_value = q l := rfl

theorem canonicalQSeriesAuditPacket_q_eq_prime :
    (canonicalQSeriesAuditPacket l).q_value =
      (l.value : ℚ_[l.value]) :=
  (canonicalQSeriesAuditPacket l).q_eq_prime

theorem canonicalQSeriesAuditPacket_q_contracts :
    ‖(canonicalQSeriesAuditPacket l).q_value‖ < 1 := by
  simpa using (canonicalQSeriesAuditPacket l).q_contracts

theorem canonicalQSeriesAuditPacket_denominator_units {n : ℕ}
    (hn : 0 < n) :
    IsUnit (1 - (canonicalQSeriesAuditPacket l).q_value ^ n) := by
  simpa using (canonicalQSeriesAuditPacket l).denominator_units hn

theorem canonicalQSeriesAuditPacket_series_summable (weight : ℕ) :
    Summable (fun n : ℕ => term l weight n) := by
  exact (canonicalQSeriesAuditPacket l).series_summable weight

theorem canonicalQSeriesAuditPacket_principal_norm (weight : ℕ) :
    ‖principal l weight‖ =
      ‖(canonicalQSeriesAuditPacket l).q_value‖ := by
  simpa using (canonicalQSeriesAuditPacket l).principal_norm weight

theorem canonicalQSeriesAuditPacket_tail_dominance (weight : ℕ) :
    ‖tail l weight‖ <
      ‖(canonicalQSeriesAuditPacket l).q_value‖ := by
  simpa using (canonicalQSeriesAuditPacket l).tail_dominance weight

theorem canonicalQSeriesAuditPacket_coefficients :
    TateCurve.a4 ℚ_[l.value] (q l) ≠ 0 ∧
      TateCurve.a6 ℚ_[l.value] (q l) ≠ 0 ∧
        (canonicalCurve l).c₄ ≠ 0 := by
  exact ⟨a4_ne_zero l, a6_ne_zero l, c4_ne_zero l⟩

theorem canonicalQSeriesAuditPacket_delta_boundary :
    (canonicalCurve l).IsElliptic ↔ discriminantNonzeroObligation l := by
  exact (discriminantNonzeroObligation_iff_elliptic l).symm

theorem canonicalQSeriesAuditPacket_is_reusable (weight : ℕ) :
    ‖q l‖ < 1 ∧
    Summable (fun n : ℕ => term l weight n) ∧
      ‖tail l weight‖ < ‖q l‖ := by
  exact ⟨q_norm_lt_one l, term_summable l weight,
    tail_norm_lt_first l weight⟩

end CanonicalQSeriesAuditPacket

section SourceFacingChain

def sourceQSeriesInput : Prop :=
  ‖q l‖ < 1 ∧
    (∀ {n : ℕ}, 0 < n → IsUnit (1 - q l ^ n)) ∧
    (∀ weight : ℕ, Summable (fun n : ℕ => term l weight n)) ∧
    localCoefficientPacket l

theorem sourceQSeriesInput_exists : sourceQSeriesInput l := by
  refine ⟨q_norm_lt_one l, ?_, ?_, localCoefficientPacket_exists l⟩
  · intro n hn
    exact denominator_is_unit l hn
  · intro weight
    exact term_summable l weight

theorem sourceQSeriesInput_q_contracts :
    sourceQSeriesInput l → ‖q l‖ < 1 := by
  intro h
  exact h.1

theorem sourceQSeriesInput_denominators :
    sourceQSeriesInput l →
      ∀ {n : ℕ}, 0 < n → IsUnit (1 - q l ^ n) := by
  intro h
  exact h.2.1

theorem sourceQSeriesInput_series_summable :
    sourceQSeriesInput l →
      ∀ weight : ℕ, Summable (fun n : ℕ => term l weight n) := by
  intro h
  exact h.2.2.1

theorem sourceQSeriesInput_integral_packet :
    sourceQSeriesInput l → localCoefficientPacket l := by
  intro h
  exact h.2.2.2

def sourceCoefficientOutput : Prop :=
  TateCurve.a4 ℚ_[l.value] (q l) ≠ 0 ∧
    TateCurve.a6 ℚ_[l.value] (q l) ≠ 0 ∧
    (canonicalCurve l).c₄ ≠ 0 ∧
    IsUnit (canonicalCurve l).c₄

theorem sourceQSeriesInput_to_coefficientOutput :
    sourceQSeriesInput l → sourceCoefficientOutput l := by
  intro _
  exact ⟨a4_ne_zero l, a6_ne_zero l, c4_ne_zero l, c4_is_unit l⟩

theorem sourceCoefficientOutput_exists : sourceCoefficientOutput l := by
  exact sourceQSeriesInput_to_coefficientOutput l (sourceQSeriesInput_exists l)

theorem sourceCoefficientOutput_a4 :
    sourceCoefficientOutput l →
      TateCurve.a4 ℚ_[l.value] (q l) ≠ 0 := by
  intro h
  exact h.1

theorem sourceCoefficientOutput_a6 :
    sourceCoefficientOutput l →
      TateCurve.a6 ℚ_[l.value] (q l) ≠ 0 := by
  intro h
  exact h.2.1

theorem sourceCoefficientOutput_c4 :
    sourceCoefficientOutput l → (canonicalCurve l).c₄ ≠ 0 := by
  intro h
  exact h.2.2.1

theorem sourceCoefficientOutput_c4_unit :
    sourceCoefficientOutput l → IsUnit (canonicalCurve l).c₄ := by
  intro h
  exact h.2.2.2

def sourceEllipticOutput : Prop :=
  sourceCoefficientOutput l ∧ discriminantNonzeroObligation l

theorem sourceEllipticOutput_to_elliptic :
    sourceEllipticOutput l → (canonicalCurve l).IsElliptic := by
  rintro ⟨_, hΔ⟩
  exact (discriminantNonzeroObligation_iff_elliptic l).mp hΔ

theorem sourceEllipticOutput_to_sourceCoefficientOutput :
    sourceEllipticOutput l → sourceCoefficientOutput l := by
  intro h
  exact h.1

theorem sourceEllipticOutput_delta_component :
    sourceEllipticOutput l → discriminantNonzeroObligation l := by
  intro h
  exact h.2

theorem sourceEllipticOutput_iff_delta_given_input :
    (sourceCoefficientOutput l ∧ discriminantNonzeroObligation l) ↔
      (sourceCoefficientOutput l ∧ (canonicalCurve l).IsElliptic) := by
  constructor
  · rintro ⟨hc, hΔ⟩
    exact ⟨hc, (discriminantNonzeroObligation_iff_elliptic l).mp hΔ⟩
  · rintro ⟨hc, hE⟩
    exact ⟨hc, (discriminantNonzeroObligation_iff_elliptic l).mpr hE⟩

theorem sourceQSeriesInput_has_no_hidden_delta_assumption :
    sourceQSeriesInput l →
      ((sourceCoefficientOutput l ∧ discriminantNonzeroObligation l) ↔
        discriminantNonzeroObligation l) := by
  intro h
  constructor
  · intro hx
    exact hx.2
  · intro hΔ
    exact ⟨sourceQSeriesInput_to_coefficientOutput l h, hΔ⟩

theorem qSeries_chain_summary :
    sourceQSeriesInput l ∧
      sourceCoefficientOutput l ∧
      (discriminantNonzeroObligation l ↔ (canonicalCurve l).IsElliptic) := by
  refine ⟨sourceQSeriesInput_exists l, sourceCoefficientOutput_exists l, ?_⟩
  exact discriminantNonzeroObligation_iff_elliptic l

theorem qSeries_chain_principal_estimate (weight : ℕ) :
    sourceQSeriesInput l →
      ‖series l weight‖ = ‖q l‖ ∧
        ‖series l weight - principal l weight‖ < ‖q l‖ := by
  intro _
  rw [series_norm_eq_first]
  refine ⟨?_, ?_⟩
  · rfl
  · rw [series_minus_principal_is_tail]
    exact tail_norm_lt_first l weight

theorem qSeries_chain_integral_presentation :
    sourceQSeriesInput l →
      ∃ W : WeierstrassCurve ℤ_[l.value],
        W.map (algebraMap (ℤ_[l.value]) (ℚ_[l.value])) = canonicalCurve l := by
  intro h
  exact localPacket_has_integral_presentation l h.2.2.2

theorem qSeries_chain_denominator_and_tail {weight n : ℕ}
    (hn : 0 < n) :
    IsUnit (1 - q l ^ n) ∧ ‖term l weight n‖ < 1 := by
  exact ⟨denominator_is_unit l hn, term_norm_lt_one l weight n hn⟩

theorem qSeries_chain_first_term_and_tail (weight : ℕ) :
    series l weight = principal l weight + tail l weight ∧
      ‖tail l weight‖ < ‖principal l weight‖ := by
  exact ⟨series_eq_first_plus_tail l weight,
    firstTailCertificate_tail_is_small l weight⟩

theorem qSeries_chain_a4_estimate :
    ‖TateCurve.a4 ℚ_[l.value] (q l)‖ =
      ‖(5 : ℚ_[l.value])‖ * ‖q l‖ ∧
      TateCurve.a4 ℚ_[l.value] (q l) ≠ 0 :=
  ⟨a4_norm_eq l, a4_ne_zero l⟩

theorem qSeries_chain_a6_estimate :
    ‖TateCurve.a6 ℚ_[l.value] (q l)‖ = ‖q l‖ ∧
      TateCurve.a6 ℚ_[l.value] (q l) ≠ 0 :=
  ⟨a6_norm_eq l, a6_ne_zero l⟩

theorem qSeries_chain_c4_estimate :
    ‖(canonicalCurve l).c₄‖ = 1 ∧
      IsUnit (canonicalCurve l).c₄ :=
  ⟨c4_norm_eq_one l, c4_is_unit l⟩

theorem qSeries_chain_stop_before_discriminant :
    sourceQSeriesInput l →
      sourceCoefficientOutput l ∧
        (discriminantNonzeroObligation l ↔ (canonicalCurve l).IsElliptic) := by
  intro h
  exact ⟨sourceQSeriesInput_to_coefficientOutput l h,
    discriminantNonzeroObligation_iff_elliptic l⟩

theorem qSeries_chain_delta_is_explicit_goal :
    discriminantNonzeroObligation l ↔ (canonicalCurve l).Δ ≠ 0 := by
  rfl

theorem qSeries_chain_delta_is_not_used_for_term_bounds :
    sourceQSeriesInput l →
      (∀ weight : ℕ, ‖tail l weight‖ < ‖q l‖) := by
  intro _ weight
  exact tail_norm_lt_first l weight

theorem qSeries_chain_integral_and_unit_data :
    localCoefficientPacket l := localCoefficientPacket_exists l

end SourceFacingChain

theorem q_series_principal_term_estimate (weight : ℕ) :
    ‖series l weight‖ = ‖q l‖ ∧
      ‖tail l weight‖ < ‖q l‖ := by
  exact ⟨series_norm_eq_first l weight, tail_norm_lt_first l weight⟩

theorem q_series_coefficients_are_nonzero :
    TateCurve.a4 ℚ_[l.value] (q l) ≠ 0 ∧
      TateCurve.a6 ℚ_[l.value] (q l) ≠ 0 :=
  ⟨a4_ne_zero l, a6_ne_zero l⟩

end AuditBoundary

end TateCurvePadic

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def tateCurvePadicEstimates : Obligation :=
  { id := "Foundations.Geometry.tate-curve-padic-estimates"
    source := "IUT I, Definition 3.1(c); p-adic q-series principal-term analysis"
    status := VerificationStatus.proved
    note :=
      "For every prime label l >= 5, the actual q=l element of Q_l has " ++
        "proved denominator norm one, coefficient-term geometric bounds, " ++
        "finite-shift tail decompositions, and strict first-term dominance. " ++
        "Consequently the canonical q-series coefficients a4, a6 and c4 are " ++
        "nonzero. This does not prove the canonical discriminant nonzero, " ++
        "Tate uniformization, split multiplicative reduction of an input curve, " ++
        "or any source-faithful Hodge-theater identification."
    dependsOn :=
      [ "Foundations.Geometry.tate-curve-arithmetic",
        "Foundations.Arithmetic.prime-label-ge-five" ] }

end LeanFormal.IUT.Audit
