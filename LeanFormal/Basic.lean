import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

open Filter Topology

namespace LeanFormal

private lemma secondOrderQuotientLimit
    (g g1 g2 : ℝ → ℝ) (c : ℝ)
    (hg : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt g (g1 x) x)
    (hg1 : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt g1 (g2 x) x)
    (hg0 : Tendsto g (𝓝 (0 : ℝ)) (𝓝 0))
    (hg10 : Tendsto g1 (𝓝 (0 : ℝ)) (𝓝 0))
    (hg2 : Tendsto g2 (𝓝 (0 : ℝ)) (𝓝 c)) :
    Tendsto (fun x : ℝ => g x / x ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 (c / 2)) := by
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0) := continuousAt_id
  have hfirst :
      Tendsto (fun x : ℝ => g1 x / (2 * x)) (𝓝[≠] (0 : ℝ)) (𝓝 (c / 2)) := by
    apply HasDerivAt.lhopital_zero_nhds hg1
    · exact .of_forall fun x => by
        exact hasDerivAt_const_mul (x := x) (2 : ℝ)
    · exact .of_forall fun _ => by norm_num
    · exact hg10
    · simpa using (tendsto_const_nhds.mul hx0)
    · simpa using hg2.div_const (2 : ℝ)
  apply HasDerivAt.lhopital_zero_nhdsNE
  · exact hg.filter_mono inf_le_left
  · exact .of_forall fun x => by
      simpa using hasDerivAt_pow 2 x
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    exact mul_ne_zero (by norm_num) hx
  · exact hg0.mono_left inf_le_left
  · have hpow : Tendsto (fun x : ℝ => x ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using hx0.pow 2
    exact hpow.mono_left inf_le_left
  · exact hfirst

private lemma logDenominatorHasDerivAt (x : ℝ) (hx : (1 + x) ≠ 0 ∧ (1 - x) ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log (1 + y) + Real.log (1 - y))
      ((1 + x)⁻¹ - (1 - x)⁻¹) x := by
  have hplus : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
  have hminus : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id x).const_sub 1
  simpa only [Function.comp_apply, Pi.add_apply, mul_one, mul_neg, sub_eq_add_neg] using!
    ((Real.hasDerivAt_log hx.1).comp x hplus).add
      ((Real.hasDerivAt_log hx.2).comp x hminus)

private lemma logDenominatorDerivHasDerivAt
    (x : ℝ) (hx : (1 + x) ≠ 0 ∧ (1 - x) ≠ 0) :
    HasDerivAt (fun y : ℝ => (1 + y)⁻¹ - (1 - y)⁻¹)
      (-1 / (1 + x) ^ 2 - 1 / (1 - x) ^ 2) x := by
  have hplus : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
  have hminus : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id x).const_sub 1
  simpa [sub_eq_add_neg] using! (hplus.inv hx.1).sub (hminus.inv hx.2)

private lemma logDenominatorSecondDerivLimit :
    Tendsto (fun x : ℝ => -1 / (1 + x) ^ 2 - 1 / (1 - x) ^ 2)
    (𝓝 (0 : ℝ)) (𝓝 (-2 : ℝ)) := by
  have hcont : ContinuousAt (fun x : ℝ => -1 / (1 + x) ^ 2 - 1 / (1 - x) ^ 2) 0 := by
    fun_prop (disch := norm_num)
  change Tendsto (fun x : ℝ => -1 / (1 + x) ^ 2 - 1 / (1 - x) ^ 2)
    (𝓝 (0 : ℝ)) (𝓝 ((-1 / (1 + (0 : ℝ)) ^ 2 - 1 / (1 - (0 : ℝ)) ^ 2))) at hcont
  norm_num at hcont
  simpa only [one_div] using hcont

private lemma logDenominatorLimit :
    Tendsto (fun x : ℝ => (Real.log (1 + x) + Real.log (1 - x)) / x ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (-1 : ℝ)) := by
  have hne : ∀ᶠ x in 𝓝 (0 : ℝ), (1 + x) ≠ 0 ∧ (1 - x) ≠ 0 := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
      (show (0 : ℝ) < 1 by norm_num)] with x hx
    simp only [Set.mem_Ioo] at hx
    constructor <;> linarith
  have hg : ∀ᶠ x in 𝓝 (0 : ℝ),
      HasDerivAt (fun y : ℝ => Real.log (1 + y) + Real.log (1 - y))
        ((1 + x)⁻¹ - (1 - x)⁻¹) x := hne.mono logDenominatorHasDerivAt
  have hg1 : ∀ᶠ x in 𝓝 (0 : ℝ),
      HasDerivAt (fun y : ℝ => (1 + y)⁻¹ - (1 - y)⁻¹)
        (-1 / (1 + x) ^ 2 - 1 / (1 - x) ^ 2) x :=
    hne.mono logDenominatorDerivHasDerivAt
  have hg0 : Tendsto (fun x : ℝ => Real.log (1 + x) + Real.log (1 - x))
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hcont := (logDenominatorHasDerivAt 0 (by norm_num)).continuousAt
    change Tendsto (fun x : ℝ => Real.log (1 + x) + Real.log (1 - x))
      (𝓝 (0 : ℝ)) (𝓝 ((fun x : ℝ => Real.log (1 + x) + Real.log (1 - x)) 0)) at hcont
    norm_num at hcont
    exact hcont
  have hg10 : Tendsto (fun x : ℝ => (1 + x)⁻¹ - (1 - x)⁻¹)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hcont := (logDenominatorDerivHasDerivAt 0 (by norm_num)).continuousAt
    change Tendsto (fun x : ℝ => (1 + x)⁻¹ - (1 - x)⁻¹)
      (𝓝 (0 : ℝ)) (𝓝 ((fun x : ℝ => (1 + x)⁻¹ - (1 - x)⁻¹) 0)) at hcont
    norm_num at hcont
    exact hcont
  simpa using secondOrderQuotientLimit
    (fun x : ℝ => Real.log (1 + x) + Real.log (1 - x))
    (fun x : ℝ => (1 + x)⁻¹ - (1 - x)⁻¹)
    (fun x : ℝ => -1 / (1 + x) ^ 2 - 1 / (1 - x) ^ 2)
    (-2) hg hg1 hg0 hg10 logDenominatorSecondDerivLimit

private lemma expResidualHasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (2 * Real.sin y) - 1 - 2 * y)
      (Real.exp (2 * Real.sin x) * (2 * Real.cos x) - 2) x := by
  have hu : HasDerivAt (fun y : ℝ => 2 * Real.sin y) (2 * Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul 2
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (2 * Real.sin y))
      (Real.exp (2 * Real.sin x) * (2 * Real.cos x)) x :=
    by simpa only [Function.comp_apply] using!
      (Real.hasDerivAt_exp (2 * Real.sin x)).comp x hu
  simpa only [sub_eq_add_neg] using!
    (hexp.sub_const 1).sub (hasDerivAt_const_mul (x := x) (2 : ℝ))

private lemma expResidualDerivHasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (2 * Real.sin y) * (2 * Real.cos y) - 2)
      ((Real.exp (2 * Real.sin x) * (2 * Real.cos x)) * (2 * Real.cos x) +
        Real.exp (2 * Real.sin x) * (2 * (-Real.sin x))) x := by
  have hu : HasDerivAt (fun y : ℝ => 2 * Real.sin y) (2 * Real.cos x) x :=
    (Real.hasDerivAt_sin x).const_mul 2
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (2 * Real.sin y))
      (Real.exp (2 * Real.sin x) * (2 * Real.cos x)) x :=
    by simpa only [Function.comp_apply] using!
      (Real.hasDerivAt_exp (2 * Real.sin x)).comp x hu
  have hcos : HasDerivAt (fun y : ℝ => 2 * Real.cos y) (2 * (-Real.sin x)) x :=
    (Real.hasDerivAt_cos x).const_mul 2
  simpa only using! (hexp.mul hcos).sub_const 2

private lemma expResidualSecondDerivLimit :
    Tendsto
      (fun x : ℝ =>
        (Real.exp (2 * Real.sin x) * (2 * Real.cos x)) * (2 * Real.cos x) +
          Real.exp (2 * Real.sin x) * (2 * (-Real.sin x)))
      (𝓝 (0 : ℝ)) (𝓝 (4 : ℝ)) := by
  have hcont : ContinuousAt
      (fun x : ℝ =>
        (Real.exp (2 * Real.sin x) * (2 * Real.cos x)) * (2 * Real.cos x) +
          Real.exp (2 * Real.sin x) * (2 * (-Real.sin x))) 0 := by
    fun_prop
  change Tendsto
    (fun x : ℝ =>
      (Real.exp (2 * Real.sin x) * (2 * Real.cos x)) * (2 * Real.cos x) +
        Real.exp (2 * Real.sin x) * (2 * (-Real.sin x)))
    (𝓝 (0 : ℝ))
    (𝓝 ((fun x : ℝ =>
      (Real.exp (2 * Real.sin x) * (2 * Real.cos x)) * (2 * Real.cos x) +
        Real.exp (2 * Real.sin x) * (2 * (-Real.sin x))) 0)) at hcont
  norm_num at hcont
  simpa only [mul_neg] using hcont

private lemma expResidualLimit :
    Tendsto (fun x : ℝ => (Real.exp (2 * Real.sin x) - 1 - 2 * x) / x ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (2 : ℝ)) := by
  have hg0 : Tendsto (fun x : ℝ => Real.exp (2 * Real.sin x) - 1 - 2 * x)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hcont := (expResidualHasDerivAt 0).continuousAt
    change Tendsto (fun x : ℝ => Real.exp (2 * Real.sin x) - 1 - 2 * x)
      (𝓝 (0 : ℝ))
      (𝓝 ((fun x : ℝ => Real.exp (2 * Real.sin x) - 1 - 2 * x) 0)) at hcont
    norm_num at hcont
    exact hcont
  have hg10 : Tendsto
      (fun x : ℝ => Real.exp (2 * Real.sin x) * (2 * Real.cos x) - 2)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hcont := (expResidualDerivHasDerivAt 0).continuousAt
    change Tendsto
      (fun x : ℝ => Real.exp (2 * Real.sin x) * (2 * Real.cos x) - 2)
      (𝓝 (0 : ℝ))
      (𝓝 ((fun x : ℝ => Real.exp (2 * Real.sin x) * (2 * Real.cos x) - 2) 0)) at hcont
    norm_num at hcont
    exact hcont
  have h := secondOrderQuotientLimit
    (fun x : ℝ => Real.exp (2 * Real.sin x) - 1 - 2 * x)
    (fun x : ℝ => Real.exp (2 * Real.sin x) * (2 * Real.cos x) - 2)
    (fun x : ℝ =>
      (Real.exp (2 * Real.sin x) * (2 * Real.cos x)) * (2 * Real.cos x) +
        Real.exp (2 * Real.sin x) * (2 * (-Real.sin x)))
    4 (.of_forall expResidualHasDerivAt) (.of_forall expResidualDerivHasDerivAt)
    hg0 hg10 expResidualSecondDerivLimit
  norm_num at h
  exact h

/-- The formal version of the problem. The conclusion directly supplies the derivative at zero. -/
theorem hasDerivAt_five_of_limit
    (f : ℝ → ℝ)
    (hf : ContinuousAt f 0)
    (hlim : Tendsto
      (fun x : ℝ =>
        (x * f x - Real.exp (2 * Real.sin x) + 1) /
          (Real.log (1 + x) + Real.log (1 - x)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-3 : ℝ))) :
    HasDerivAt f 5 0 := by
  let L : Filter ℝ := 𝓝[≠] (0 : ℝ)
  have hx0 : Tendsto (fun x : ℝ => x) L (𝓝 0) := by
    exact (show Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0) from continuousAt_id).mono_left
      inf_le_left
  have hnum2 : Tendsto
      (fun x : ℝ => (x * f x - Real.exp (2 * Real.sin x) + 1) / x ^ 2)
      L (𝓝 (3 : ℝ)) := by
    have hprod := hlim.mul logDenominatorLimit
    norm_num at hprod
    refine hprod.congr' ?_
    have hratioNonzero : ∀ᶠ x in L,
        (Real.log (1 + x) + Real.log (1 - x)) / x ^ 2 ≠ 0 :=
      logDenominatorLimit.eventually_ne (show (-1 : ℝ) ≠ 0 by norm_num)
    filter_upwards [hratioNonzero, self_mem_nhdsWithin] with x hratio hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    have hden : Real.log (1 + x) + Real.log (1 - x) ≠ 0 := by
      intro hzero
      simp [hzero] at hratio
    field_simp [hden, hx]
  have hnum1 : Tendsto
      (fun x : ℝ => (x * f x - Real.exp (2 * Real.sin x) + 1) / x)
      L (𝓝 (0 : ℝ)) := by
    have hmul := hnum2.mul hx0
    norm_num at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    field_simp [hx]
  have hexpResidual1 : Tendsto
      (fun x : ℝ => (Real.exp (2 * Real.sin x) - 1 - 2 * x) / x)
      L (𝓝 (0 : ℝ)) := by
    have hmul := expResidualLimit.mul hx0
    norm_num at hmul
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    field_simp [hx]
  have hexp1 : Tendsto
      (fun x : ℝ => (Real.exp (2 * Real.sin x) - 1) / x)
      L (𝓝 (2 : ℝ)) := by
    have hconst : Tendsto (fun _ : ℝ => (2 : ℝ)) L (𝓝 2) := tendsto_const_nhds
    have hadd := hexpResidual1.add hconst
    norm_num at hadd
    refine hadd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    field_simp [hx]
    ring
  have hf2 : Tendsto f L (𝓝 (2 : ℝ)) := by
    have hadd := hnum1.add hexp1
    norm_num at hadd
    refine hadd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    field_simp [hx]
    ring
  have hf0 : f 0 = 2 := tendsto_nhds_unique'
    (NormedField.nhdsNE_neBot (0 : ℝ)) (hf.mono_left inf_le_left) hf2
  have hslope : Tendsto (fun x : ℝ => (f x - f 0) / x) L (𝓝 (5 : ℝ)) := by
    have hadd := hnum2.add expResidualLimit
    norm_num at hadd
    refine hadd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    rw [hf0]
    field_simp [hx]
    ring
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simpa only [zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using hslope

/-- The conclusion in the exact form requested by the problem. -/
theorem differentiableAt_and_deriv_eq_five
    (f : ℝ → ℝ)
    (hf : ContinuousAt f 0)
    (hlim : Tendsto
      (fun x : ℝ =>
        (x * f x - Real.exp (2 * Real.sin x) + 1) /
          (Real.log (1 + x) + Real.log (1 - x)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (-3 : ℝ))) :
    DifferentiableAt ℝ f 0 ∧ deriv f 0 = 5 := by
  have hderiv := hasDerivAt_five_of_limit f hf hlim
  exact ⟨hderiv.differentiableAt, hderiv.deriv⟩

end LeanFormal
