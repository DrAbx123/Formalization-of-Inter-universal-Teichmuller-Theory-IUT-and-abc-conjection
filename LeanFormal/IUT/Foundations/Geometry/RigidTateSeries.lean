/-
  Laurent-series terms for the Tate parameterization.

  The two half-series are kept separate.  This is the correct formal shape
  for a non-archimedean Laurent series indexed by `ℤ`: it avoids silently
  replacing a bilateral convergence statement by a natural-number series.
-/

import LeanFormal.IUT.Foundations.Geometry.RigidTateAnnulus
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace LeanFormal.IUT

universe u

noncomputable section

namespace RigidTate

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

abbrev FundamentalDomain (P : Parameter (K := K)) := Shell P 0

namespace FundamentalDomain

variable (P : Parameter (K := K))

theorem ne_zero (u : FundamentalDomain P) : u.1 ≠ 0 :=
  Shell.ne_zero P 0 u

theorem norm_pos (u : FundamentalDomain P) : 0 < ‖u.1‖ :=
  Shell.norm_pos P 0 u

theorem q_lt_norm (u : FundamentalDomain P) :
    ‖P.q‖ < ‖u.1‖ := by
  simpa using Shell.inner P 0 u

theorem norm_lt_one (u : FundamentalDomain P) :
    ‖u.1‖ < 1 := by
  simpa using Shell.outer P 0 u

end FundamentalDomain

/-- The two radial pieces of the Tate Laurent series. -/
def positiveArgument (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) : K :=
  P.q ^ (n : ℤ) * u.1

def negativeArgument (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) : K :=
  P.q ^ (-(n + 1 : ℕ) : ℤ) * u.1

namespace Argument

variable (P : Parameter (K := K)) (u : FundamentalDomain P)

@[simp] theorem positiveArgument_zero : positiveArgument P u 0 = u := by
  simp [positiveArgument]

@[simp] theorem positiveArgument_succ (n : ℕ) :
    positiveArgument P u (n + 1) = P.q ^ (n + 1 : ℤ) * u.1 :=
  rfl

theorem positiveArgument_ne_zero (n : ℕ) :
    positiveArgument P u n ≠ 0 := by
  exact mul_ne_zero (Parameter.q_zpow_ne_zero P n) u.ne_zero

theorem positiveArgument_norm (n : ℕ) :
    ‖positiveArgument P u n‖ = ‖P.q‖ ^ (n : ℤ) * ‖u.1‖ := by
  simp [positiveArgument, Parameter.norm_q_zpow]

theorem positiveArgument_norm_lt_one (n : ℕ) :
    ‖positiveArgument P u n‖ < 1 := by
  rw [positiveArgument_norm]
  have hq : ‖P.q‖ ^ (n : ℤ) ≤ 1 := by
    cases n with
    | zero => simp
    | succ n =>
        exact (Parameter.norm_q_zpow_lt_one P (n + 1 : ℤ) (by omega)).le
  have hu := FundamentalDomain.norm_lt_one P u
  have hq0 : 0 ≤ ‖P.q‖ ^ (n : ℤ) :=
    (Parameter.norm_q_zpow_pos P (n : ℤ)).le
  have hu0 : 0 ≤ ‖u.1‖ := norm_nonneg _
  nlinarith

theorem positiveArgument_sub_one_norm (n : ℕ) :
    ‖1 - positiveArgument P u n‖ = 1 := by
  have harg := positiveArgument_norm_lt_one P u n
  have hupper : ‖1 - positiveArgument P u n‖ ≤ 1 := by
    calc
      ‖1 - positiveArgument P u n‖ ≤
          max ‖(1 : K)‖ ‖positiveArgument P u n‖ :=
        IsUltrametricDist.norm_sub_le _ _
      _ ≤ 1 := by simp [harg.le]
  have hlower : 1 ≤ ‖1 - positiveArgument P u n‖ := by
    have h := IsUltrametricDist.norm_add_le_max
      (1 - positiveArgument P u n) (positiveArgument P u n)
    have heq : (1 - positiveArgument P u n) + positiveArgument P u n = (1 : K) :=
      sub_add_cancel _ _
    rw [heq] at h
    have hmax : max ‖1 - positiveArgument P u n‖
        ‖positiveArgument P u n‖ < 1 ∨
        1 ≤ max ‖1 - positiveArgument P u n‖
        ‖positiveArgument P u n‖ := lt_or_ge _ _
    exact le_of_not_gt (fun hbad => by
      have : max ‖1 - positiveArgument P u n‖
          ‖positiveArgument P u n‖ < 1 := hbad
      exact (not_lt_of_ge h) (by simpa using h))
  exact le_antisymm hupper hlower

theorem positiveArgument_denominator_ne_zero (n : ℕ) :
    1 - positiveArgument P u n ≠ 0 := by
  intro h
  have hnorm := congrArg norm h
  rw [norm_zero, positiveArgument_sub_one_norm P u n] at hnorm
  norm_num at hnorm

theorem positiveArgument_sub_one_inverse_norm (n : ℕ) :
    ‖(1 - positiveArgument P u n)⁻¹‖ = 1 := by
  rw [norm_inv, positiveArgument_sub_one_norm P u n, inv_one]

theorem negativeArgument_ne_zero (n : ℕ) :
    negativeArgument P u n ≠ 0 := by
  exact mul_ne_zero (Parameter.q_zpow_ne_zero P (-(n + 1 : ℕ) : ℤ)) u.ne_zero

theorem negativeArgument_norm (n : ℕ) :
    ‖negativeArgument P u n‖ =
      (‖P.q‖ ^ (n + 1 : ℤ))⁻¹ * ‖u.1‖ := by
  rw [negativeArgument, norm_mul, Parameter.norm_q_zpow,
    zpow_neg₀ (Parameter.q_norm_ne_zero P), norm_inv]

theorem negativeArgument_norm_gt_one (n : ℕ) :
    1 < ‖negativeArgument P u n‖ := by
  rw [negativeArgument_norm]
  have hqpos : 0 < ‖P.q‖ ^ (n + 1 : ℤ) :=
    Parameter.norm_q_zpow_pos P (n + 1 : ℤ)
  have hinner : ‖P.q‖ ^ (n + 1 : ℤ) < ‖u.1‖ := by
    simpa using Shell.inner P 0 u
  have hdiv : 1 < ‖u.1‖ / ‖P.q‖ ^ (n + 1 : ℤ) := by
    apply (lt_div_iff₀ hqpos).2
    simpa using hinner
  simpa [div_eq_mul_inv] using hdiv

theorem negativeArgument_sub_one_norm (n : ℕ) :
    ‖1 - negativeArgument P u n‖ = ‖negativeArgument P u n‖ := by
  have harg := negativeArgument_norm_gt_one P u n
  have hupper : ‖1 - negativeArgument P u n‖ ≤
      ‖negativeArgument P u n‖ := by
    calc
      ‖1 - negativeArgument P u n‖ ≤
          max ‖(1 : K)‖ ‖negativeArgument P u n‖ :=
        IsUltrametricDist.norm_sub_le _ _
      _ = ‖negativeArgument P u n‖ := by
        rw [max_eq_right (le_of_lt harg)]
  have hlower : ‖negativeArgument P u n‖ ≤
      ‖1 - negativeArgument P u n‖ := by
    have h := IsUltrametricDist.norm_add_le_max
      (1 - negativeArgument P u n) (negativeArgument P u n)
    have heq : (1 - negativeArgument P u n) + negativeArgument P u n = (1 : K) :=
      sub_add_cancel _ _
    rw [heq] at h
    have hnormone : (1 : ℝ) < ‖negativeArgument P u n‖ := harg
    by_contra hnot
    have hlt : ‖negativeArgument P u n‖ >
        ‖1 - negativeArgument P u n‖ := lt_of_not_ge hnot
    have hmax : max ‖1 - negativeArgument P u n‖
        ‖negativeArgument P u n‖ = ‖negativeArgument P u n‖ :=
      max_eq_right (le_of_lt hlt)
    rw [hmax] at h
    linarith
  exact le_antisymm hupper hlower

theorem negativeArgument_denominator_ne_zero (n : ℕ) :
    1 - negativeArgument P u n ≠ 0 := by
  intro h
  have hnorm := congrArg norm h
  rw [norm_zero, negativeArgument_sub_one_norm P u n] at hnorm
  have hpos := (negativeArgument_norm_gt_one P u n).trans_le
    (le_of_eq hnorm.symm)
  linarith

end Argument

def xPositiveTerm (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) : K :=
  positiveArgument P u n /
    (1 - positiveArgument P u n) ^ 2

def xNegativeTerm (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) : K :=
  negativeArgument P u n /
    (1 - negativeArgument P u n) ^ 2

def yPositiveTerm (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) : K :=
  positiveArgument P u n ^ 2 /
    (1 - positiveArgument P u n) ^ 3

def yNegativeTerm (P : Parameter (K := K))
    (u : FundamentalDomain P) (n : ℕ) : K :=
  negativeArgument P u n ^ 2 /
    (1 - negativeArgument P u n) ^ 3

namespace Term

variable (P : Parameter (K := K)) (u : FundamentalDomain P)

theorem xPositiveTerm_norm_le (n : ℕ) :
    ‖xPositiveTerm P u n‖ ≤ ‖P.q‖ ^ (n : ℤ) * ‖u.1‖ := by
  rw [xPositiveTerm, norm_div, norm_pow,
    Argument.positiveArgument_sub_one_inverse_norm P u n,
    mul_one, Argument.positiveArgument_norm]

theorem yPositiveTerm_norm_le (n : ℕ) :
    ‖yPositiveTerm P u n‖ ≤
      (‖P.q‖ ^ (n : ℤ) * ‖u.1‖) ^ 2 := by
  rw [yPositiveTerm, norm_div, norm_pow,
    Argument.positiveArgument_sub_one_inverse_norm P u n,
    mul_one, Argument.positiveArgument_norm]

theorem xNegativeTerm_norm_le (n : ℕ) :
    ‖xNegativeTerm P u n‖ ≤
      (‖P.q‖ ^ (n + 1 : ℤ)) ^ 1 := by
  rw [xNegativeTerm, norm_div, norm_pow,
    Argument.negativeArgument_sub_one_norm P u n,
    norm_pow, div_self (by
      exact ne_of_gt (Argument.negativeArgument_norm_gt_one P u n))]

theorem yNegativeTerm_norm_le (n : ℕ) :
    ‖yNegativeTerm P u n‖ ≤
      (‖P.q‖ ^ (n + 1 : ℤ)) ^ 1 := by
  rw [yNegativeTerm, norm_div, norm_pow,
    Argument.negativeArgument_sub_one_norm P u n,
    norm_pow]
  have h : 0 < ‖negativeArgument P u n‖ :=
    (Argument.negativeArgument_norm_gt_one P u n).trans_le (by norm_num)
  field_simp
  exact le_rfl

end Term

/-- One-sided sums are the actual convergent pieces of the Tate x-coordinate. -/
def xPositiveSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) : K :=
  ∑' n : ℕ, xPositiveTerm P u n

def xNegativeSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) : K :=
  ∑' n : ℕ, xNegativeTerm P u n

def yPositiveSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) : K :=
  ∑' n : ℕ, yPositiveTerm P u n

def yNegativeSeries (P : Parameter (K := K))
    (u : FundamentalDomain P) : K :=
  ∑' n : ℕ, yNegativeTerm P u n

end RigidTate

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def rigidTateLaurentTerms : Obligation :=
  { id := "Foundations.Geometry.rigid-tate-laurent-terms"
    source := "Tate uniformization: Laurent coordinate terms on |q|<|u|<1"
    status := VerificationStatus.interface
    note :=
      "The two-sided Tate x/y summands are defined on the genuine " ++
        "non-archimedean fundamental annulus, with proved nonvanishing " ++
        "denominators and radial norm estimates. The remaining summability " ++
        "and the Weierstrass equation identity are the next analytic proof " ++
        "obligations; no point map is claimed yet."
    dependsOn := [ "Foundations.Geometry.rigid-tate-annulus" ] }

end LeanFormal.IUT.Audit
