/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Stage1.IUTStage1Remark312Absorption

/-!
IUT IV algebraic and analytic shadow estimates used by the Stage 1 corridor.

This module is a mechanical extraction from `Iut.Stage1.IUTStage1Source`.  It
keeps the Remark 3.12 sign shadows, theta-pilot coefficient estimates, and
IUT IV Theorem 1.10 / Corollary 2.2 / Theorem A handoff shadows separate from
the finite-label, Hodge/SHE, IPL, and Step (xi) source-route declarations.
-/

namespace Iut
namespace Stage1

open RealLineCopy
open scoped BigOperators

universe u v w x

/--
Remark 3.12.3(i) Gauss--Bonnet metric sign shadow.

Mochizuki compares the Corollary 3.12 inequality to the classical formula
`chi_S = - ∫_S dmu_S < 0` for a hyperbolic Riemann surface, where positivity of
the metric volume gives the negative Euler characteristic.  This record keeps
only that sign calculation and its role as the metric analogue of the `(Ind3)`
upper-semi inequality.
-/
structure IUTStage1GaussBonnetMetricSignShadow where
  metricVolume : Real
  metric_volume_pos : 0 < metricVolume
  eulerCharacteristic : Real
  euler_eq_neg_metricVolume :
    eulerCharacteristic = -metricVolume
  upperSemiInd3Analogue : Prop
  upper_semi_ind3_analogue :
    upperSemiInd3Analogue

namespace IUTStage1GaussBonnetMetricSignShadow

theorem eulerCharacteristic_neg
    (data : IUTStage1GaussBonnetMetricSignShadow) :
    data.eulerCharacteristic < 0 := by
  rw [data.euler_eq_neg_metricVolume]
  linarith [data.metric_volume_pos]

theorem eulerCharacteristic_nonpos
    (data : IUTStage1GaussBonnetMetricSignShadow) :
    data.eulerCharacteristic <= 0 :=
  le_of_lt data.eulerCharacteristic_neg

theorem metricVolume_ne_zero
    (data : IUTStage1GaussBonnetMetricSignShadow) :
    data.metricVolume ≠ 0 :=
  ne_of_gt data.metric_volume_pos

theorem upperSemiInd3Analogue_holds
    (data : IUTStage1GaussBonnetMetricSignShadow) :
    data.upperSemiInd3Analogue :=
  data.upper_semi_ind3_analogue

theorem eulerCharacteristic_ne_zero
    (data : IUTStage1GaussBonnetMetricSignShadow) :
    data.eulerCharacteristic ≠ 0 :=
  ne_of_lt data.eulerCharacteristic_neg

theorem gauss_bonnet_metric_endpoint
    (data : IUTStage1GaussBonnetMetricSignShadow) :
    data.eulerCharacteristic < 0 ∧
      data.eulerCharacteristic <= 0 ∧ data.upperSemiInd3Analogue :=
  ⟨data.eulerCharacteristic_neg, data.eulerCharacteristic_nonpos,
    data.upperSemiInd3Analogue_holds⟩

end IUTStage1GaussBonnetMetricSignShadow

/--
Remark 3.12.4(iii) theta-label factor-`p` normalization shadow.

The source text compares procession-normalized volumes obtained by averaging
over `j ∈ F_l` with dividing by the factor `p` that relates the mod `p/p^2`
portion of Witt vectors to the mod `p` portion.  In the IUT label model the
finite factor is `l`, so this record keeps the corresponding real normalization.
-/
structure IUTStage1ThetaLabelFactorPNormalizationShadow where
  l : PrimeGeFive
  modPOverP2GapLogVolume : Real
  normalizedModPLogVolume : Real
  normalized_eq_div_l :
    normalizedModPLogVolume =
      modPOverP2GapLogVolume / (l.value : Real)

namespace IUTStage1ThetaLabelFactorPNormalizationShadow

theorem labelFactor_ne_zero
    (data : IUTStage1ThetaLabelFactorPNormalizationShadow) :
    (data.l.value : Real) ≠ 0 := by
  exact_mod_cast data.l.ne_zero

theorem labelFactor_pos
    (data : IUTStage1ThetaLabelFactorPNormalizationShadow) :
    0 < (data.l.value : Real) := by
  exact_mod_cast Nat.pos_of_ne_zero data.l.ne_zero

theorem normalized_mul_labelFactor
    (data : IUTStage1ThetaLabelFactorPNormalizationShadow) :
    data.normalizedModPLogVolume * (data.l.value : Real) =
      data.modPOverP2GapLogVolume := by
  rw [data.normalized_eq_div_l]
  exact div_mul_cancel₀ data.modPOverP2GapLogVolume data.labelFactor_ne_zero

theorem normalized_eq_factor_average
    (data : IUTStage1ThetaLabelFactorPNormalizationShadow) :
    data.normalizedModPLogVolume =
      data.modPOverP2GapLogVolume / (data.l.value : Real) :=
  data.normalized_eq_div_l

theorem normalized_nonpos_iff_gap_nonpos
    (data : IUTStage1ThetaLabelFactorPNormalizationShadow) :
    data.normalizedModPLogVolume <= 0 ↔
      data.modPOverP2GapLogVolume <= 0 := by
  constructor
  · intro hnorm
    have hmul := data.normalized_mul_labelFactor
    have hpos := data.labelFactor_pos
    nlinarith
  · intro hgap
    have hmul := data.normalized_mul_labelFactor
    have hpos := data.labelFactor_pos
    nlinarith

theorem factor_normalization_order_endpoint
    (data : IUTStage1ThetaLabelFactorPNormalizationShadow) :
    data.normalizedModPLogVolume * (data.l.value : Real) =
        data.modPOverP2GapLogVolume ∧
      (data.normalizedModPLogVolume <= 0 ↔
        data.modPOverP2GapLogVolume <= 0) :=
  ⟨data.normalized_mul_labelFactor, data.normalized_nonpos_iff_gap_nonpos⟩

end IUTStage1ThetaLabelFactorPNormalizationShadow

/--
Remark 3.12.4(v) p-adic Frobenius derivative degree inequality.

The source text says that the derivative of the canonical Frobenius lifting,
after division by `p`, yields an inclusion of line bundles
`omega_Xk -> Phi^* omega_Xk`, not an isomorphism.  At degree level this gives
the inequality `(1 - p) * (2g_X - 2) <= 0`.  This record keeps only that
degree-level sign shadow and the inclusion-not-isomorphism marker.
-/
structure IUTStage1FrobeniusDerivativeDegreeInequalityShadow where
  p : Nat
  p_ge_two : 2 <= p
  genus : Nat
  genus_ge_two : 2 <= genus
  derivativeGivesInclusion : Prop
  derivative_gives_inclusion : derivativeGivesInclusion
  derivativeIsomorphismNotAssumed : Prop
  derivative_isomorphism_not_assumed :
    derivativeIsomorphismNotAssumed

namespace IUTStage1FrobeniusDerivativeDegreeInequalityShadow

def degreeDefect
    (data : IUTStage1FrobeniusDerivativeDegreeInequalityShadow) :
    Real :=
  ((1 : Real) - (data.p : Real)) *
    ((2 : Real) * (data.genus : Real) - 2)

theorem one_le_p_real
    (data : IUTStage1FrobeniusDerivativeDegreeInequalityShadow) :
    (1 : Real) <= data.p := by
  exact_mod_cast le_trans (by decide : 1 <= 2) data.p_ge_two

theorem genus_term_nonneg
    (data : IUTStage1FrobeniusDerivativeDegreeInequalityShadow) :
    (0 : Real) <= (2 : Real) * (data.genus : Real) - 2 := by
  have hgenus : (2 : Real) <= data.genus := by
    exact_mod_cast data.genus_ge_two
  nlinarith

theorem genus_term_pos
    (data : IUTStage1FrobeniusDerivativeDegreeInequalityShadow) :
    (0 : Real) < (2 : Real) * (data.genus : Real) - 2 := by
  have hgenus : (2 : Real) <= data.genus := by
    exact_mod_cast data.genus_ge_two
  nlinarith

theorem degreeDefect_nonpos
    (data : IUTStage1FrobeniusDerivativeDegreeInequalityShadow) :
    data.degreeDefect <= 0 := by
  have hp : (1 : Real) - (data.p : Real) <= 0 := by
    linarith [data.one_le_p_real]
  exact mul_nonpos_of_nonpos_of_nonneg hp data.genus_term_nonneg

theorem degreeDefect_neg
    (data : IUTStage1FrobeniusDerivativeDegreeInequalityShadow) :
    data.degreeDefect < 0 := by
  have hp : (1 : Real) - (data.p : Real) < 0 := by
    have hp2 : (2 : Real) <= data.p := by
      exact_mod_cast data.p_ge_two
    linarith
  exact mul_neg_of_neg_of_pos hp data.genus_term_pos

theorem degreeDefect_ne_zero
    (data : IUTStage1FrobeniusDerivativeDegreeInequalityShadow) :
    data.degreeDefect ≠ 0 :=
  ne_of_lt data.degreeDefect_neg

theorem derivativeGivesInclusion_holds
    (data : IUTStage1FrobeniusDerivativeDegreeInequalityShadow) :
    data.derivativeGivesInclusion :=
  data.derivative_gives_inclusion

theorem derivativeIsomorphismNotAssumed_holds
    (data : IUTStage1FrobeniusDerivativeDegreeInequalityShadow) :
    data.derivativeIsomorphismNotAssumed :=
  data.derivative_isomorphism_not_assumed

theorem derivative_degree_endpoint
    (data : IUTStage1FrobeniusDerivativeDegreeInequalityShadow) :
    data.derivativeGivesInclusion ∧
      data.derivativeIsomorphismNotAssumed ∧
        data.degreeDefect <= 0 ∧ data.degreeDefect < 0 :=
  ⟨data.derivativeGivesInclusion_holds,
    data.derivativeIsomorphismNotAssumed_holds,
    data.degreeDefect_nonpos,
    data.degreeDefect_neg⟩

end IUTStage1FrobeniusDerivativeDegreeInequalityShadow

/--
IUT IV, Theorem 1.10 arithmetic upper term for the constant `C_Theta`.

This is the explicit non-negative side of the displayed expression for `C_Theta`
before subtracting the logarithmic term and `1`.  The construction of the
arithmetic divisors is not included here; their log-degrees enter as real
parameters.
-/
noncomputable def iutIVThetaPilotArithmeticUpperTerm
    (l : PrimeGeFive) (dmod : Nat) (absoluteLogQ logDifferentFtpd
      logConductorFtpd eStarMod etaPrm : Real) : Real :=
  (((l.value : Real) + 1) / (4 * absoluteLogQ)) *
      (1 + 12 * (dmod : Real) / (l.value : Real)) *
      (logDifferentFtpd + logConductorFtpd) +
    10 * (eStarMod * (l.value : Real) + etaPrm)

/--
IUT IV, Theorem 1.10 logarithmic term subtracted from the upper expression for
`C_Theta`.
-/
noncomputable def iutIVThetaPilotMainLogTerm (l : PrimeGeFive) (logQ : Real) : Real :=
  ((1 : Real) / 6) * (1 - 12 / ((l.value : Real) ^ 2)) * logQ

/-- The correction factor `1 - 12/l^2` appearing in IUT IV, Theorem 1.10. -/
noncomputable def iutIVThetaPilotCorrectionFactor (l : PrimeGeFive) : Real :=
  1 - 12 / ((l.value : Real) ^ 2)

/-- The small correction between the main IUT IV logarithmic term and `(1/6)log(q)`. -/
noncomputable def iutIVThetaPilotCorrectionLogTerm (l : PrimeGeFive) (logQ : Real) : Real :=
  ((1 : Real) / 6) * (12 / ((l.value : Real) ^ 2)) * logQ

/-- The left side of the final displayed log-volume estimate in IUT IV, Theorem 1.10. -/
noncomputable def iutIVThetaPilotOneSixthLogQ (logQ : Real) : Real :=
  ((1 : Real) / 6) * logQ

/-- IUT IV, Theorem 1.10 final right-hand side after the elementary estimates. -/
noncomputable def iutIVThetaPilotTheorem110RightHandSide
    (l : PrimeGeFive) (dmod : Nat) (logDifferentFtpd logConductorFtpd
      eStarMod etaPrm : Real) : Real :=
  (1 + 20 * (dmod : Real) / (l.value : Real)) *
      (logDifferentFtpd + logConductorFtpd) +
    20 * (eStarMod * (l.value : Real) + etaPrm)

/-- First elementary estimate in the final paragraph of IUT IV, Theorem 1.10. -/
theorem iutIVThetaPilotCorrectionFactor_pos (l : PrimeGeFive) :
    0 < iutIVThetaPilotCorrectionFactor l := by
  rw [iutIVThetaPilotCorrectionFactor]
  have hl : (5 : Real) <= (l.value : Real) := by exact_mod_cast l.ge_five
  have hsq : (0 : Real) < (l.value : Real) ^ 2 := by positivity
  have hdiv : (12 : Real) / ((l.value : Real) ^ 2) < 1 := by
    rw [div_lt_iff₀ hsq]
    nlinarith
  linarith

/-- The displayed estimate `(1 - 12/l^2)^(-1) <= 2` for `l >= 5`. -/
theorem iutIVThetaPilotCorrectionFactor_inv_le_two (l : PrimeGeFive) :
    (iutIVThetaPilotCorrectionFactor l)⁻¹ <= (2 : Real) := by
  have hpos := iutIVThetaPilotCorrectionFactor_pos l
  have hl : (5 : Real) <= (l.value : Real) := by exact_mod_cast l.ge_five
  have hsq : (0 : Real) < (l.value : Real) ^ 2 := by positivity
  have htwentyfour : (24 : Real) <= (l.value : Real) ^ 2 := by nlinarith
  have hdiv : (12 : Real) / ((l.value : Real) ^ 2) <= (1 : Real) / 2 := by
    rw [div_le_iff₀ hsq]
    nlinarith
  have hhalf : (1 : Real) / 2 <= iutIVThetaPilotCorrectionFactor l := by
    rw [iutIVThetaPilotCorrectionFactor]
    linarith
  rw [inv_le_comm₀ hpos (by norm_num : (0 : Real) < 2)]
  nlinarith

/--
Second elementary estimate in the final paragraph of IUT IV, Theorem 1.10.

The paper records
`(1 - 12/l^2)^(-1) * 1/4 * (1 + 12*dmod/l) <= 1 + 20*dmod/l`
using `l >= 5` and `dmod >= 1`; nonnegativity of `dmod` is already built into
the present natural-number parameter.
-/
theorem iutIVThetaPilotFinalCoefficientEstimate
    (l : PrimeGeFive) (dmod : Nat) :
    (iutIVThetaPilotCorrectionFactor l)⁻¹ * ((1 : Real) / 4) *
        (1 + 12 * (dmod : Real) / (l.value : Real)) <=
      1 + 20 * (dmod : Real) / (l.value : Real) := by
  have hfactor := iutIVThetaPilotCorrectionFactor_inv_le_two l
  have hl : (0 : Real) < (l.value : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero l.ne_zero
  have hcoeff_nonneg :
      0 <= ((1 : Real) / 4) *
        (1 + 12 * (dmod : Real) / (l.value : Real)) := by
    positivity
  calc
    (iutIVThetaPilotCorrectionFactor l)⁻¹ * ((1 : Real) / 4) *
        (1 + 12 * (dmod : Real) / (l.value : Real))
        =
      (iutIVThetaPilotCorrectionFactor l)⁻¹ *
        (((1 : Real) / 4) *
          (1 + 12 * (dmod : Real) / (l.value : Real))) := by
          ring
    _ <=
      2 *
        (((1 : Real) / 4) *
          (1 + 12 * (dmod : Real) / (l.value : Real))) := by
          exact mul_le_mul_of_nonneg_right hfactor hcoeff_nonneg
    _ = (1 : Real) / 2 +
        6 * ((dmod : Real) / (l.value : Real)) := by
          ring
    _ <= 1 + 20 * ((dmod : Real) / (l.value : Real)) := by
      have hdl : 0 <= (dmod : Real) / (l.value : Real) := by positivity
      nlinarith
    _ = 1 + 20 * (dmod : Real) / (l.value : Real) := by
      ring

/--
IUT IV, Theorem 1.10, Step (i), identity (E1), before division by `n`.

The sum is written over `range (n+1)`, so the zero term is harmless and the
range is exactly `0, ..., n`.
-/
theorem iutIVThetaPilot_sum_id_mul_two (n : Nat) :
    (∑ m ∈ Finset.range (n + 1), (m : Real)) * 2 =
      (n : Real) * ((n : Real) + 1) := by
  have hnat := Finset.sum_range_id_mul_two (n + 1)
  have hnat' :
      (∑ m ∈ Finset.range (n + 1), m) * 2 = (n + 1) * n := by
    simpa using hnat
  have hreal :
      (∑ m ∈ Finset.range (n + 1), (m : Real)) * 2 =
        ((n + 1 : Nat) * n : Real) := by
    rw [← Nat.cast_sum, ← Nat.cast_mul]
    exact_mod_cast hnat'
  calc
    (∑ m ∈ Finset.range (n + 1), (m : Real)) * 2 =
        ((n + 1 : Nat) * n : Real) := hreal
    _ = (n : Real) * ((n : Real) + 1) := by
      norm_num
      ring

/-- IUT IV, Theorem 1.10, Step (i), identity (E1). -/
theorem iutIVThetaPilot_average_sum_id
    (n : Nat) (hn : 1 <= n) :
    (∑ m ∈ Finset.range (n + 1), (m : Real)) / (n : Real) =
      ((n : Real) + 1) / 2 := by
  have hraw := iutIVThetaPilot_sum_id_mul_two n
  have hn_ne : (n : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn_ne]
  linarith

/-- IUT IV, Theorem 1.10, Step (i), identity (E2), before division by `n`. -/
theorem iutIVThetaPilot_sum_sq_mul_six (n : Nat) :
    (∑ m ∈ Finset.range (n + 1), (m : Real) ^ 2) * 6 =
      (n : Real) * ((n : Real) + 1) * (2 * (n : Real) + 1) := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        ((∑ m ∈ Finset.range (n + 1), (m : Real) ^ 2) +
            ((n + 1 : Nat) : Real) ^ 2) * 6 =
          (∑ m ∈ Finset.range (n + 1), (m : Real) ^ 2) * 6 +
            ((n + 1 : Nat) : Real) ^ 2 * 6 := by
            ring
        _ = (n : Real) * ((n : Real) + 1) * (2 * (n : Real) + 1) +
            ((n + 1 : Nat) : Real) ^ 2 * 6 := by
            rw [ih]
        _ = ((n + 1 : Nat) : Real) * (((n + 1 : Nat) : Real) + 1) *
            (2 * (((n + 1 : Nat) : Real)) + 1) := by
            norm_num
            ring

/-- IUT IV, Theorem 1.10, Step (i), identity (E2). -/
theorem iutIVThetaPilot_average_sum_sq
    (n : Nat) (hn : 1 <= n) :
    (∑ m ∈ Finset.range (n + 1), (m : Real) ^ 2) / (n : Real) =
      (1 / 6 : Real) * (2 * (n : Real) + 1) * ((n : Real) + 1) := by
  have hraw := iutIVThetaPilot_sum_sq_mul_six n
  have hn_ne : (n : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn_ne]
  ring_nf at hraw ⊢
  nlinarith

/-- IUT IV, Theorem 1.10, Step (i), formula (E3) as a numerical expression. -/
def iutIVGLTwoCardinalityExpression (p : Nat) : Nat :=
  p * (p + 1) * (p - 1) ^ 2

/-- IUT IV, Theorem 1.10, Step (i), formula (E4), the case `p = 2`. -/
theorem iutIVGLTwoCardinalityExpression_two :
    iutIVGLTwoCardinalityExpression 2 = 2 * 3 := by
  norm_num [iutIVGLTwoCardinalityExpression]

/-- IUT IV, Theorem 1.10, Step (i), formula (E4), the case `p = 3`. -/
theorem iutIVGLTwoCardinalityExpression_three :
    iutIVGLTwoCardinalityExpression 3 = 3 * 2 ^ 4 := by
  norm_num [iutIVGLTwoCardinalityExpression]

/-- IUT IV, Theorem 1.10, Step (i), formula (E4), the case `p = 5`. -/
theorem iutIVGLTwoCardinalityExpression_five :
    iutIVGLTwoCardinalityExpression 5 = 5 * 2 ^ 5 * 3 := by
  norm_num [iutIVGLTwoCardinalityExpression]

/--
The product of the Step (i) `p = 2,3,5` cardinality expressions and the quadratic
factor from (E5).  This is the arithmetic core used before the coarser
small-prime logarithmic bound in Step (ii).
-/
def iutIVSmallPrimeGLTwoDegreeExpression : Nat :=
  iutIVGLTwoCardinalityExpression 2 *
    iutIVGLTwoCardinalityExpression 3 *
    iutIVGLTwoCardinalityExpression 5 *
    2

theorem iutIVSmallPrimeGLTwoDegreeExpression_eq :
    iutIVSmallPrimeGLTwoDegreeExpression = 2 ^ 11 * 3 ^ 3 * 5 := by
  norm_num [iutIVSmallPrimeGLTwoDegreeExpression,
    iutIVGLTwoCardinalityExpression]

/--
IUT IV, Theorem 1.10, Step (ii), small-prime ramification error.

The paper bounds the contribution from the primes dividing `2 * 3 * 5` by
`log(2^11 * 3^3 * 5^2) <= 21`, using the elementary logarithmic estimates in
(E6).  This record keeps only the real-valued upper-bound calculation.
-/
structure IUTStage1IUTIVSmallPrimeRamificationErrorBoundShadow where
  logTwo : Real
  logThree : Real
  logFive : Real
  logTwo_le_one : logTwo <= 1
  logThree_le_two : logThree <= 2
  logFive_le_two : logFive <= 2

namespace IUTStage1IUTIVSmallPrimeRamificationErrorBoundShadow

def smallPrimeError
    (data : IUTStage1IUTIVSmallPrimeRamificationErrorBoundShadow) : Real :=
  11 * data.logTwo + 3 * data.logThree + 2 * data.logFive

theorem smallPrimeError_le_twentyOne
    (data : IUTStage1IUTIVSmallPrimeRamificationErrorBoundShadow) :
    data.smallPrimeError <= 21 := by
  rw [smallPrimeError]
  nlinarith [data.logTwo_le_one, data.logThree_le_two, data.logFive_le_two]

end IUTStage1IUTIVSmallPrimeRamificationErrorBoundShadow

/--
IUT IV, Theorem 1.10, Step (ii), additive log-degree error bound.

This packages the formal shape of the displayed estimate
`log(d_F)+log(f_F) <= log(d_Ftpd)+log(f_Ftpd)+21` once the finite small-prime
error has been bounded by `21`.
-/
structure IUTStage1IUTIVTameRamificationLogDegreeErrorShadow where
  ftpdLogDegreeSum : Real
  fLogDegreeSum : Real
  smallPrimeError :
    IUTStage1IUTIVSmallPrimeRamificationErrorBoundShadow
  f_le_ftpd_add_smallPrimeError :
    fLogDegreeSum <= ftpdLogDegreeSum + smallPrimeError.smallPrimeError

namespace IUTStage1IUTIVTameRamificationLogDegreeErrorShadow

theorem fLogDegreeSum_le_ftpd_add_twentyOne
    (data : IUTStage1IUTIVTameRamificationLogDegreeErrorShadow) :
    data.fLogDegreeSum <= data.ftpdLogDegreeSum + 21 := by
  exact le_trans data.f_le_ftpd_add_smallPrimeError
    (add_le_add le_rfl data.smallPrimeError.smallPrimeError_le_twentyOne)

end IUTStage1IUTIVTameRamificationLogDegreeErrorShadow

/--
IUT IV, Theorem 1.10, Step (iii), the algebraic `log(s_Q)` estimate.

The source combines the Step (ii) estimate for `log(d_K)+log(f_K)` with
`log(s_Q) <= 2*dmod*(log(d_Ftpd)+log(f_Ftpd))+5+log(l)`, then absorbs the
coefficients to obtain the displayed bound with coefficient
`1 + 36*dmod/l`.  The elementary estimate used here is `2*log(l) <= l`, valid
for the source range `l >= 5`.  The construction of `s_Q` is not formalized
here; its displayed real-valued bound is an explicit hypothesis.
-/
structure IUTStage1IUTIVLogSQStepIIIShadow where
  l : PrimeGeFive
  dmod : Nat
  dmod_ge_one : 1 <= dmod
  ftpdLogDegreeSum : Real
  ftpdLogDegreeSum_nonneg : 0 <= ftpdLogDegreeSum
  logKDegreeSum : Real
  logSQ : Real
  logL : Real
  two_logL_le_l : 2 * logL <= (l.value : Real)
  logKDegreeSum_bound :
    logKDegreeSum <= ftpdLogDegreeSum + 2 * logL + 21
  logSQ_bound :
    logSQ <= 2 * (dmod : Real) * ftpdLogDegreeSum + 5 + logL

namespace IUTStage1IUTIVLogSQStepIIIShadow

noncomputable def leftHandSide
    (data : IUTStage1IUTIVLogSQStepIIIShadow) : Real :=
  (1 + 4 / (data.l.value : Real)) * data.logKDegreeSum +
    (16 / (data.l.value : Real)) * data.logSQ

noncomputable def rightHandSide
    (data : IUTStage1IUTIVLogSQStepIIIShadow) : Real :=
  (1 + 36 * (data.dmod : Real) / (data.l.value : Real)) *
      data.ftpdLogDegreeSum +
    2 * data.logL + 70

theorem leftHandSide_le_rightHandSide
    (data : IUTStage1IUTIVLogSQStepIIIShadow) :
    data.leftHandSide <= data.rightHandSide := by
  have hlpos : (0 : Real) < (data.l.value : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero data.l.ne_zero
  have hlfive : (5 : Real) <= (data.l.value : Real) := by
    exact_mod_cast data.l.ge_five
  have hdmod : (1 : Real) <= (data.dmod : Real) := by
    exact_mod_cast data.dmod_ge_one
  have hcoeffK : 0 <= (1 : Real) + 4 / (data.l.value : Real) := by
    positivity
  have hcoeffSQ : 0 <= (16 : Real) / (data.l.value : Real) := by
    positivity
  have hK :=
    mul_le_mul_of_nonneg_left data.logKDegreeSum_bound hcoeffK
  have hSQ :=
    mul_le_mul_of_nonneg_left data.logSQ_bound hcoeffSQ
  have hcombined := add_le_add hK hSQ
  have halgebra :
      (1 + 4 / (data.l.value : Real)) *
          (data.ftpdLogDegreeSum + 2 * data.logL + 21) +
        (16 / (data.l.value : Real)) *
          (2 * (data.dmod : Real) * data.ftpdLogDegreeSum + 5 +
            data.logL) <=
        (1 + 36 * (data.dmod : Real) / (data.l.value : Real)) *
          data.ftpdLogDegreeSum +
        2 * data.logL + 70 := by
    field_simp [ne_of_gt hlpos]
    nlinarith [hlfive, hdmod, data.ftpdLogDegreeSum_nonneg, data.two_logL_le_l]
  dsimp [leftHandSide, rightHandSide] at hcombined ⊢
  exact le_trans hcombined halgebra

end IUTStage1IUTIVLogSQStepIIIShadow

/--
IUT IV, Theorem 1.10, Step (viii), Proposition 1.6 prime-product bound.

The source treats separately the cases `e*_mod*l >= eta_prm` and
`e*_mod*l < eta_prm`, then records the uniform estimate
`l*_mod*log(s_<=) <= 4/3*(e*_mod*l + eta_prm)`.  This record keeps exactly that
case split at the real-valued level.
-/
structure IUTStage1IUTIVPrimeProductCaseSplitBoundShadow where
  primeProductLogTerm : Real
  eStarTimesL : Real
  etaPrm : Real
  eStarTimesL_nonneg : 0 <= eStarTimesL
  etaPrm_nonneg : 0 <= etaPrm
  large_case_bound :
    etaPrm <= eStarTimesL ->
      primeProductLogTerm <= (4 / 3 : Real) * eStarTimesL
  small_case_bound :
    eStarTimesL < etaPrm ->
      primeProductLogTerm <= (4 / 3 : Real) * etaPrm

namespace IUTStage1IUTIVPrimeProductCaseSplitBoundShadow

theorem primeProductLogTerm_le_uniform
    (data : IUTStage1IUTIVPrimeProductCaseSplitBoundShadow) :
    data.primeProductLogTerm <=
      (4 / 3 : Real) * (data.eStarTimesL + data.etaPrm) := by
  by_cases hlarge : data.etaPrm <= data.eStarTimesL
  · have hcase := data.large_case_bound hlarge
    have heta : 0 <= (4 / 3 : Real) * data.etaPrm :=
      mul_nonneg (by norm_num) data.etaPrm_nonneg
    nlinarith
  · have hsmall : data.eStarTimesL < data.etaPrm := lt_of_not_ge hlarge
    have hcase := data.small_case_bound hsmall
    have he : 0 <= (4 / 3 : Real) * data.eStarTimesL :=
      mul_nonneg (by norm_num) data.eStarTimesL_nonneg
    nlinarith

end IUTStage1IUTIVPrimeProductCaseSplitBoundShadow

/--
IUT IV, Theorem 1.10, Step (viii), final coarse error absorption.

After bounding the prime-product term by `4/3*(e*_mod*l+eta_prm)`, the source
uses a separate lower estimate for `e*_mod*l+eta_prm` to absorb the remaining
`2*log(l)+74` term and replace the accumulated constants by
`10*(e*_mod*l+eta_prm)`.
-/
structure IUTStage1IUTIVFinalErrorAbsorptionShadow where
  primeProductLogTerm : Real
  eEta : Real
  logL : Real
  eEta_nonneg : 0 <= eEta
  primeProduct_bound :
    primeProductLogTerm <= (4 / 3 : Real) * eEta
  log_error_bound :
    2 * logL + 74 <= (4 / 9 : Real) * eEta

namespace IUTStage1IUTIVFinalErrorAbsorptionShadow

theorem finalError_le_ten
    (data : IUTStage1IUTIVFinalErrorAbsorptionShadow) :
    2 * data.logL + 74 + (20 / 3 : Real) * data.primeProductLogTerm <=
      10 * data.eEta := by
  have hprimeScaled :
      (20 / 3 : Real) * data.primeProductLogTerm <=
        (20 / 3 : Real) * ((4 / 3 : Real) * data.eEta) := by
    exact mul_le_mul_of_nonneg_left data.primeProduct_bound (by norm_num)
  nlinarith [data.log_error_bound, hprimeScaled, data.eEta_nonneg]

end IUTStage1IUTIVFinalErrorAbsorptionShadow

/--
IUT IV, Theorem 1.10 and Step (ii): replacing the tripodal intermediate field
by the larger field in the final displayed estimate.

The source justification is the inequality
`log(d_Ftpd) + log(f_Ftpd) <= log(d_F) + log(f_F)`, derived from Proposition
1.3(i) and the definitions.  This record isolates exactly the real-valued
log-degree monotonicity needed by the final line of the theorem.
-/
structure IUTStage1IUTIVTripodalBaseChangeLogDegreeShadow where
  l : PrimeGeFive
  dmod : Nat
  logDifferentFtpd : Real
  logConductorFtpd : Real
  logDifferentF : Real
  logConductorF : Real
  eStarMod : Real
  etaPrm : Real
  different_le : logDifferentFtpd <= logDifferentF
  conductor_le : logConductorFtpd <= logConductorF

namespace IUTStage1IUTIVTripodalBaseChangeLogDegreeShadow

def ftpdLogDegreeSum
    (data : IUTStage1IUTIVTripodalBaseChangeLogDegreeShadow) : Real :=
  data.logDifferentFtpd + data.logConductorFtpd

def fLogDegreeSum
    (data : IUTStage1IUTIVTripodalBaseChangeLogDegreeShadow) : Real :=
  data.logDifferentF + data.logConductorF

noncomputable def coefficient
    (data : IUTStage1IUTIVTripodalBaseChangeLogDegreeShadow) : Real :=
  1 + 20 * (data.dmod : Real) / (data.l.value : Real)

noncomputable def ftpdTheorem110RightHandSide
    (data : IUTStage1IUTIVTripodalBaseChangeLogDegreeShadow) : Real :=
  iutIVThetaPilotTheorem110RightHandSide data.l data.dmod
    data.logDifferentFtpd data.logConductorFtpd data.eStarMod data.etaPrm

noncomputable def fTheorem110RightHandSide
    (data : IUTStage1IUTIVTripodalBaseChangeLogDegreeShadow) : Real :=
  iutIVThetaPilotTheorem110RightHandSide data.l data.dmod
    data.logDifferentF data.logConductorF data.eStarMod data.etaPrm

theorem logDegreeSum_le
    (data : IUTStage1IUTIVTripodalBaseChangeLogDegreeShadow) :
    data.ftpdLogDegreeSum <= data.fLogDegreeSum :=
  add_le_add data.different_le data.conductor_le

theorem coefficient_nonneg
    (data : IUTStage1IUTIVTripodalBaseChangeLogDegreeShadow) :
    0 <= data.coefficient := by
  rw [coefficient]
  positivity

theorem ftpdTheorem110RightHandSide_le_fTheorem110RightHandSide
    (data : IUTStage1IUTIVTripodalBaseChangeLogDegreeShadow) :
    data.ftpdTheorem110RightHandSide <= data.fTheorem110RightHandSide := by
  have hsum := data.logDegreeSum_le
  have hcoeff := data.coefficient_nonneg
  dsimp [ftpdTheorem110RightHandSide, fTheorem110RightHandSide,
    iutIVThetaPilotTheorem110RightHandSide, ftpdLogDegreeSum,
    fLogDegreeSum, coefficient] at hsum hcoeff ⊢
  exact add_le_add (mul_le_mul_of_nonneg_left hsum hcoeff) le_rfl

end IUTStage1IUTIVTripodalBaseChangeLogDegreeShadow

/--
IUT IV, Theorem 1.10 shadow of the `C_Theta` handoff.

The source text computes an explicit expression for `C_Theta` and then applies
the Corollary 3.12 lower bound `C_Theta >= -1`.  This record keeps precisely
that algebraic interface: the exact displayed expression, the Corollary 3.12
lower bound, and a separate field for the remaining elementary estimates that
convert the intermediate logarithmic term to the final right-hand side.
-/
structure IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow where
  l : PrimeGeFive
  dmod : Nat
  logQ : Real
  absoluteLogQ : Real
  logQ_pos : 0 < logQ
  absoluteLogQ_eq : absoluteLogQ = (1 / (2 * (l.value : Real))) * logQ
  logDifferentFtpd : Real
  logConductorFtpd : Real
  eStarMod : Real
  etaPrm : Real
  cTheta : Real
  cTheta_eq :
    cTheta =
      iutIVThetaPilotArithmeticUpperTerm l dmod absoluteLogQ
        logDifferentFtpd logConductorFtpd eStarMod etaPrm -
        iutIVThetaPilotMainLogTerm l logQ - 1
  cor312_lower_bound : (-1 : Real) <= cTheta
  explicit_estimates_to_theorem110_rhs :
    iutIVThetaPilotArithmeticUpperTerm l dmod absoluteLogQ
        logDifferentFtpd logConductorFtpd eStarMod etaPrm +
        iutIVThetaPilotCorrectionLogTerm l logQ <=
      iutIVThetaPilotTheorem110RightHandSide l dmod
        logDifferentFtpd logConductorFtpd eStarMod etaPrm

namespace IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow

noncomputable def arithmeticUpperTerm
    (data : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) : Real :=
  iutIVThetaPilotArithmeticUpperTerm data.l data.dmod data.absoluteLogQ
    data.logDifferentFtpd data.logConductorFtpd data.eStarMod data.etaPrm

noncomputable def mainLogTerm
    (data : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) : Real :=
  iutIVThetaPilotMainLogTerm data.l data.logQ

noncomputable def correctionLogTerm
    (data : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) : Real :=
  iutIVThetaPilotCorrectionLogTerm data.l data.logQ

noncomputable def oneSixthLogQ
    (data : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) : Real :=
  iutIVThetaPilotOneSixthLogQ data.logQ

noncomputable def theorem110RightHandSide
    (data : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) : Real :=
  iutIVThetaPilotTheorem110RightHandSide data.l data.dmod
    data.logDifferentFtpd data.logConductorFtpd data.eStarMod data.etaPrm

theorem absoluteLogQ_pos
    (data : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) :
    0 < data.absoluteLogQ := by
  rw [data.absoluteLogQ_eq]
  have hl : (0 : Real) < (data.l.value : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero data.l.ne_zero
  have hden : (0 : Real) < 2 * (data.l.value : Real) := by positivity
  exact mul_pos (one_div_pos.mpr hden) data.logQ_pos

theorem cTheta_expression
    (data : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) :
    data.cTheta = data.arithmeticUpperTerm - data.mainLogTerm - 1 :=
  data.cTheta_eq

theorem cTheta_add_one_eq_arithmetic_minus_main
    (data : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) :
    data.cTheta + 1 = data.arithmeticUpperTerm - data.mainLogTerm := by
  rw [data.cTheta_expression]
  ring

theorem arithmetic_minus_main_nonneg
    (data : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) :
    0 <= data.arithmeticUpperTerm - data.mainLogTerm := by
  have h := data.cor312_lower_bound
  rw [data.cTheta_expression] at h
  linarith

theorem mainLogTerm_le_arithmeticUpperTerm
    (data : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) :
    data.mainLogTerm <= data.arithmeticUpperTerm := by
  linarith [data.arithmetic_minus_main_nonneg]

theorem oneSixthLogQ_eq_main_add_correction
    (data : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) :
    data.oneSixthLogQ = data.mainLogTerm + data.correctionLogTerm := by
  rw [oneSixthLogQ, mainLogTerm, correctionLogTerm,
    iutIVThetaPilotOneSixthLogQ, iutIVThetaPilotMainLogTerm,
    iutIVThetaPilotCorrectionLogTerm]
  ring

theorem oneSixthLogQ_le_theorem110RightHandSide
    (data : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) :
    data.oneSixthLogQ <= data.theorem110RightHandSide := by
  rw [data.oneSixthLogQ_eq_main_add_correction]
  exact le_trans
    (add_le_add data.mainLogTerm_le_arithmeticUpperTerm le_rfl)
    data.explicit_estimates_to_theorem110_rhs

theorem corollary312_handoff_endpoint
    (data : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) :
    0 < data.absoluteLogQ ∧
      data.cTheta + 1 = data.arithmeticUpperTerm - data.mainLogTerm ∧
        0 <= data.arithmeticUpperTerm - data.mainLogTerm ∧
          data.mainLogTerm <= data.arithmeticUpperTerm ∧
            data.oneSixthLogQ <= data.theorem110RightHandSide :=
  ⟨data.absoluteLogQ_pos,
    data.cTheta_add_one_eq_arithmetic_minus_main,
    data.arithmetic_minus_main_nonneg,
    data.mainLogTerm_le_arithmeticUpperTerm,
    data.oneSixthLogQ_le_theorem110RightHandSide⟩

end IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow

set_option linter.style.longLine false in
/--
Paper-side lower-bound source for the arithmetic-degree coefficient
\(a_l\) in the IUT IV Theorem 1.10 estimate.

The coefficient
\[
  a_l=\frac{l+1}{4|\log(q)|}\left(1+\frac{12\,d_{\mathrm{mod}}}{l}\right)
\]
is used in the Step (xi) scaling argument only after proving \(1\leq a_l\).
The current shadow estimate already proves \(|\log(q)|>0\); this source names
the remaining size condition needed to turn the displayed expression into the
coefficient lower bound.
-/
structure IUTStage1IUTIVThetaPilotArithmeticDegreeCoefficientLowerBoundSource
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) where
  absoluteLogQ_degree_window :
    4 * estimate.absoluteLogQ <= (estimate.l.value : Real) + 1

namespace IUTStage1IUTIVThetaPilotArithmeticDegreeCoefficientLowerBoundSource

variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}

noncomputable def arithmeticDegreeCoefficient
    (_source :
      IUTStage1IUTIVThetaPilotArithmeticDegreeCoefficientLowerBoundSource
        estimate) :
    Real :=
  (((estimate.l.value : Real) + 1) / (4 * estimate.absoluteLogQ)) *
    (1 + 12 * (estimate.dmod : Real) / (estimate.l.value : Real))

noncomputable def baseWindowFactor
    (_source :
      IUTStage1IUTIVThetaPilotArithmeticDegreeCoefficientLowerBoundSource
        estimate) :
    Real :=
  ((estimate.l.value : Real) + 1) / (4 * estimate.absoluteLogQ)

noncomputable def thetaErrorFactor
    (_source :
      IUTStage1IUTIVThetaPilotArithmeticDegreeCoefficientLowerBoundSource
        estimate) :
    Real :=
  1 + 12 * (estimate.dmod : Real) / (estimate.l.value : Real)

theorem baseWindowFactor_ge_one
    (source :
      IUTStage1IUTIVThetaPilotArithmeticDegreeCoefficientLowerBoundSource
        estimate) :
    1 <= source.baseWindowFactor := by
  have hdenpos : 0 < 4 * estimate.absoluteLogQ := by
    exact mul_pos (by norm_num) estimate.absoluteLogQ_pos
  have hdiv :=
    div_le_div_of_nonneg_right source.absoluteLogQ_degree_window
      (le_of_lt hdenpos)
  have hself : (4 * estimate.absoluteLogQ) /
      (4 * estimate.absoluteLogQ) = (1 : Real) := by
    exact div_self (ne_of_gt hdenpos)
  simpa [baseWindowFactor, hself] using hdiv

theorem thetaErrorFactor_ge_one
    (source :
      IUTStage1IUTIVThetaPilotArithmeticDegreeCoefficientLowerBoundSource
        estimate) :
    1 <= source.thetaErrorFactor := by
  have hnonneg :
      0 <= 12 * (estimate.dmod : Real) /
          (estimate.l.value : Real) := by
    positivity
  dsimp [thetaErrorFactor]
  linarith

theorem arithmeticDegreeCoefficient_ge_one
    (source :
      IUTStage1IUTIVThetaPilotArithmeticDegreeCoefficientLowerBoundSource
        estimate) :
    1 <= source.arithmeticDegreeCoefficient := by
  have hfactor1 := source.baseWindowFactor_ge_one
  have hfactor2 := source.thetaErrorFactor_ge_one
  have hfactor2_nonneg :
      0 <= 1 + 12 * (estimate.dmod : Real) /
          (estimate.l.value : Real) :=
    le_trans (by norm_num) hfactor2
  dsimp [arithmeticDegreeCoefficient, baseWindowFactor,
    thetaErrorFactor] at hfactor1 hfactor2 hfactor2_nonneg ⊢
  nlinarith

def Endpoint
    (source :
      IUTStage1IUTIVThetaPilotArithmeticDegreeCoefficientLowerBoundSource
        estimate) :
    Prop :=
  0 < estimate.absoluteLogQ ∧
    4 * estimate.absoluteLogQ <= (estimate.l.value : Real) + 1 ∧
      1 <= source.arithmeticDegreeCoefficient

theorem endpoint
    (source :
      IUTStage1IUTIVThetaPilotArithmeticDegreeCoefficientLowerBoundSource
        estimate) :
    Endpoint source :=
  ⟨estimate.absoluteLogQ_pos,
    source.absoluteLogQ_degree_window,
    source.arithmeticDegreeCoefficient_ge_one⟩

structure CoefficientWindowAudit
    (source :
      IUTStage1IUTIVThetaPilotArithmeticDegreeCoefficientLowerBoundSource
        estimate) :
    Prop where
  absoluteLogQ_pos : 0 < estimate.absoluteLogQ
  absoluteLogQ_degree_window :
    4 * estimate.absoluteLogQ <= (estimate.l.value : Real) + 1
  baseWindowFactor_ge_one : 1 <= source.baseWindowFactor
  thetaErrorFactor_ge_one : 1 <= source.thetaErrorFactor
  arithmeticDegreeCoefficient_ge_one :
    1 <= source.arithmeticDegreeCoefficient
  endpoint : source.Endpoint

theorem coefficientWindowAudit
    (source :
      IUTStage1IUTIVThetaPilotArithmeticDegreeCoefficientLowerBoundSource
        estimate) :
    CoefficientWindowAudit source :=
  { absoluteLogQ_pos := estimate.absoluteLogQ_pos,
    absoluteLogQ_degree_window := source.absoluteLogQ_degree_window,
    baseWindowFactor_ge_one := source.baseWindowFactor_ge_one,
    thetaErrorFactor_ge_one := source.thetaErrorFactor_ge_one,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    endpoint := source.endpoint }

end IUTStage1IUTIVThetaPilotArithmeticDegreeCoefficientLowerBoundSource

set_option linter.style.longLine false in
/--
IUT IV, Definition 1.9 / Theorem 1.10 local arithmetic-divisor evaluation
source for the theta-pilot estimate.

The paper defines the different, q-parameter, and conductor-support terms as
normalized degrees of arithmetic divisors and then sums local estimates over the
relevant places.  This record isolates the part of that construction needed by
the Corollary 3.12 corridor: local different/conductor degrees, the absorbed
prime/error contribution, and local main-log contributions whose finite sums
recover the two real terms in `IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow`.
-/
structure IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
    (place : Type u) [Fintype place]
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) where
  localDifferentDegree : place -> Real
  localConductorDegree : place -> Real
  localPrimeErrorContribution : place -> Real
  localMainLogContribution : place -> Real
  localDifferentDegree_nonneg :
    ∀ v : place, 0 <= localDifferentDegree v
  localConductorDegree_nonneg :
    ∀ v : place, 0 <= localConductorDegree v
  localPrimeErrorContribution_nonneg :
    ∀ v : place, 0 <= localPrimeErrorContribution v
  logDifferentFtpd_eq_sum :
    estimate.logDifferentFtpd =
      ∑ v : place, localDifferentDegree v
  logConductorFtpd_eq_sum :
    estimate.logConductorFtpd =
      ∑ v : place, localConductorDegree v
  primeErrorContribution_eq_sum :
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ v : place, localPrimeErrorContribution v
  mainLogTerm_eq_sum :
    estimate.mainLogTerm =
      ∑ v : place, localMainLogContribution v

namespace IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}

noncomputable def arithmeticDegreeCoefficient
    (_source :
      IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
        place estimate) :
    Real :=
  (((estimate.l.value : Real) + 1) / (4 * estimate.absoluteLogQ)) *
    (1 + 12 * (estimate.dmod : Real) / (estimate.l.value : Real))

noncomputable def localArithmeticUpperContribution
    (source :
      IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
        place estimate)
    (v : place) :
    Real :=
  source.arithmeticDegreeCoefficient *
      (source.localDifferentDegree v + source.localConductorDegree v) +
    source.localPrimeErrorContribution v

theorem logDegreeSum_eq_sum
    (source :
      IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
        place estimate) :
    estimate.logDifferentFtpd + estimate.logConductorFtpd =
      ∑ v : place,
        (source.localDifferentDegree v + source.localConductorDegree v) := by
  rw [source.logDifferentFtpd_eq_sum, source.logConductorFtpd_eq_sum]
  rw [Finset.sum_add_distrib]

set_option linter.style.longLine false in
theorem arithmeticUpperTerm_eq_sum
    (source :
      IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
        place estimate) :
    estimate.arithmeticUpperTerm =
      ∑ v : place, source.localArithmeticUpperContribution v := by
  simp only [IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow.arithmeticUpperTerm,
    iutIVThetaPilotArithmeticUpperTerm, localArithmeticUpperContribution,
    arithmeticDegreeCoefficient]
  rw [source.logDifferentFtpd_eq_sum, source.logConductorFtpd_eq_sum,
    source.primeErrorContribution_eq_sum]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_add_distrib]

def Endpoint
    (source :
      IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
        place estimate) :
    Prop :=
  estimate.logDifferentFtpd =
      ∑ v : place, source.localDifferentDegree v ∧
    estimate.logConductorFtpd =
      ∑ v : place, source.localConductorDegree v ∧
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ v : place, source.localPrimeErrorContribution v ∧
    estimate.arithmeticUpperTerm =
      ∑ v : place, source.localArithmeticUpperContribution v ∧
    estimate.mainLogTerm =
      ∑ v : place, source.localMainLogContribution v

theorem endpoint
    (source :
      IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
        place estimate) :
    Endpoint source :=
  ⟨source.logDifferentFtpd_eq_sum,
    source.logConductorFtpd_eq_sum,
    source.primeErrorContribution_eq_sum,
    source.arithmeticUpperTerm_eq_sum,
    source.mainLogTerm_eq_sum⟩

end IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource

set_option linter.style.longLine false in
/--
IUT IV, Definition 1.9(i), finite arithmetic-divisor source.

The paper defines an arithmetic divisor as a finite formal sum
`∑ c_v v`, with support `{v | c_v ≠ 0}`, effectivity `0 <= c_v`,
and normalized degree obtained by weighting nonarchimedean valuations by
`log(q_v)` and archimedean valuations by `1`, then dividing by `[F : Q]`.
This finite source keeps precisely the data needed by the Stage 1
`C_Theta` corridor: coefficients, degree weights, a positive normalizing
degree, and nonnegativity of the degree weights.
-/
structure IUTStage1IUTIVArithmeticDivisorSource
    (place : Type u) [Fintype place] where
  coefficient : place -> Real
  degreeWeight : place -> Real
  fieldDegree : Real
  fieldDegree_pos : 0 < fieldDegree
  degreeWeight_nonneg : ∀ v : place, 0 <= degreeWeight v

namespace IUTStage1IUTIVArithmeticDivisorSource

variable {place : Type u} [Fintype place]

def support
    (divisor : IUTStage1IUTIVArithmeticDivisorSource place) :
    Set place :=
  {v | divisor.coefficient v ≠ 0}

def Effective
    (divisor : IUTStage1IUTIVArithmeticDivisorSource place) :
    Prop :=
  ∀ v : place, 0 <= divisor.coefficient v

noncomputable def localDegree
    (divisor : IUTStage1IUTIVArithmeticDivisorSource place)
    (v : place) :
    Real :=
  divisor.coefficient v * divisor.degreeWeight v / divisor.fieldDegree

noncomputable def degree
    (divisor : IUTStage1IUTIVArithmeticDivisorSource place) :
    Real :=
  (∑ v : place, divisor.coefficient v * divisor.degreeWeight v) /
    divisor.fieldDegree

theorem degree_eq_sum_localDegree
    (divisor : IUTStage1IUTIVArithmeticDivisorSource place) :
    divisor.degree = ∑ v : place, divisor.localDegree v := by
  simp [degree, localDegree, Finset.sum_div]

theorem localDegree_nonneg
    (divisor : IUTStage1IUTIVArithmeticDivisorSource place)
    (effective : divisor.Effective)
    (v : place) :
    0 <= divisor.localDegree v :=
  div_nonneg
    (mul_nonneg (effective v) (divisor.degreeWeight_nonneg v))
    (le_of_lt divisor.fieldDegree_pos)

theorem degree_nonneg
    (divisor : IUTStage1IUTIVArithmeticDivisorSource place)
    (effective : divisor.Effective) :
    0 <= divisor.degree := by
  rw [divisor.degree_eq_sum_localDegree]
  exact Finset.sum_nonneg
    (fun v _hv => divisor.localDegree_nonneg effective v)

theorem mem_support_iff
    (divisor : IUTStage1IUTIVArithmeticDivisorSource place)
    (v : place) :
    v ∈ divisor.support ↔ divisor.coefficient v ≠ 0 :=
  Iff.rfl

end IUTStage1IUTIVArithmeticDivisorSource

/-- Local cases of IUT IV, Theorem 1.10, Steps (v), (vi), and (vii). -/
inductive IUTStage1IUTIVTheorem110LocalEstimateKind where
  | distinguishedNonarchimedean
  | nondistinguishedNonarchimedean
  | archimedean
deriving DecidableEq

set_option linter.style.longLine false in
/--
IUT IV, Definition 1.9 / Theorem 1.10 arithmetic-divisor source.

This packages the paper's three arithmetic divisors:
`d_ADiv` from the different, `q_ADiv` from q-parameters at bad valuations,
and `f_ADiv` from the conductor support.  It also records the support/effectivity
content that is used later in Theorem 1.10: `f_ADiv` has the same support as
`q_ADiv`, and the global `log(d_Ftpd)`, `log(f_Ftpd)` quantities are the
normalized degrees of the different and conductor divisors.
-/
structure IUTStage1IUTIVTheorem110ArithmeticDivisorSource
    (place : Type u) [Fintype place]
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) where
  differentDivisor : IUTStage1IUTIVArithmeticDivisorSource place
  qParameterDivisor : IUTStage1IUTIVArithmeticDivisorSource place
  conductorDivisor : IUTStage1IUTIVArithmeticDivisorSource place
  different_effective : differentDivisor.Effective
  qParameter_effective : qParameterDivisor.Effective
  conductor_effective : conductorDivisor.Effective
  conductor_support_iff_q_support :
    ∀ v : place,
      v ∈ conductorDivisor.support ↔ v ∈ qParameterDivisor.support
  conductor_coeff_eq_one_of_q_support :
    ∀ v : place, v ∈ qParameterDivisor.support ->
      conductorDivisor.coefficient v = 1
  conductor_coeff_eq_zero_of_q_not_support :
    ∀ v : place, v ∉ qParameterDivisor.support ->
      conductorDivisor.coefficient v = 0
  logDifferentFtpd_eq_degree :
    estimate.logDifferentFtpd = differentDivisor.degree
  logConductorFtpd_eq_degree :
    estimate.logConductorFtpd = conductorDivisor.degree

namespace IUTStage1IUTIVTheorem110ArithmeticDivisorSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}

noncomputable def localDifferentDegree
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate)
    (v : place) :
    Real :=
  source.differentDivisor.localDegree v

noncomputable def localConductorDegree
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate)
    (v : place) :
    Real :=
  source.conductorDivisor.localDegree v

noncomputable def arithmeticDegreeCoefficient
    (_source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate) :
    Real :=
  (((estimate.l.value : Real) + 1) / (4 * estimate.absoluteLogQ)) *
    (1 + 12 * (estimate.dmod : Real) / (estimate.l.value : Real))

noncomputable def localArithmeticUpperContribution
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate)
    (localPrimeErrorContribution : place -> Real)
    (v : place) :
    Real :=
  source.arithmeticDegreeCoefficient *
      (source.localDifferentDegree v + source.localConductorDegree v) +
    localPrimeErrorContribution v

theorem localDifferentDegree_nonneg
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate)
    (v : place) :
    0 <= source.localDifferentDegree v :=
  source.differentDivisor.localDegree_nonneg
    source.different_effective v

theorem localConductorDegree_nonneg
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate)
    (v : place) :
    0 <= source.localConductorDegree v :=
  source.conductorDivisor.localDegree_nonneg
    source.conductor_effective v

theorem logDifferentFtpd_eq_sum
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate) :
    estimate.logDifferentFtpd =
      ∑ v : place, source.localDifferentDegree v := by
  rw [source.logDifferentFtpd_eq_degree,
    source.differentDivisor.degree_eq_sum_localDegree]
  rfl

theorem logConductorFtpd_eq_sum
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate) :
    estimate.logConductorFtpd =
      ∑ v : place, source.localConductorDegree v := by
  rw [source.logConductorFtpd_eq_degree,
    source.conductorDivisor.degree_eq_sum_localDegree]
  rfl

theorem conductor_support_eq_q_support
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate) :
    source.conductorDivisor.support = source.qParameterDivisor.support := by
  ext v
  exact source.conductor_support_iff_q_support v

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate) :
    Prop :=
  source.differentDivisor.Effective ∧
    source.qParameterDivisor.Effective ∧
      source.conductorDivisor.Effective ∧
        source.conductorDivisor.support =
          source.qParameterDivisor.support ∧
          estimate.logDifferentFtpd =
            ∑ v : place, source.localDifferentDegree v ∧
            estimate.logConductorFtpd =
              ∑ v : place, source.localConductorDegree v

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate) :
    Endpoint source :=
  ⟨source.different_effective,
    source.qParameter_effective,
    source.conductor_effective,
    source.conductor_support_eq_q_support,
    source.logDifferentFtpd_eq_sum,
    source.logConductorFtpd_eq_sum⟩

end IUTStage1IUTIVTheorem110ArithmeticDivisorSource

set_option linter.style.longLine false in
/--
IUT IV, Theorem 1.10 local estimate gates for Steps (v), (vi), and (vii).

The source text separates the local upper-bound computation into distinguished
nonarchimedean places, nondistinguished nonarchimedean places with zero
contribution, and archimedean places.  This record keeps that case distinction
and the resulting local upper-semi inequalities.  It also supplies the finite-sum
identities for the absorbed prime/error term and the main logarithmic term.
-/
structure IUTStage1IUTIVTheorem110LocalEstimateGateSource
    (place : Type u) [Fintype place]
    {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
    (divisorSource :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate) where
  localKind : place -> IUTStage1IUTIVTheorem110LocalEstimateKind
  localPrimeErrorContribution : place -> Real
  localMainLogContribution : place -> Real
  localProcessionUpperBound : place -> Real
  localPrimeErrorContribution_nonneg :
    ∀ v : place, 0 <= localPrimeErrorContribution v
  primeErrorContribution_eq_sum :
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ v : place, localPrimeErrorContribution v
  mainLogTerm_eq_sum :
    estimate.mainLogTerm =
      ∑ v : place, localMainLogContribution v
  stepV_distinguished_le_gap :
    ∀ v : place,
      localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
        localProcessionUpperBound v <=
          divisorSource.localArithmeticUpperContribution
              localPrimeErrorContribution v -
            localMainLogContribution v
  stepVI_nondistinguished_zero :
    ∀ v : place,
      localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean ->
        localProcessionUpperBound v = 0
  stepVI_nondistinguished_le_gap :
    ∀ v : place,
      localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean ->
        localProcessionUpperBound v <=
          divisorSource.localArithmeticUpperContribution
              localPrimeErrorContribution v -
            localMainLogContribution v
  stepVII_archimedean_le_gap :
    ∀ v : place,
      localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
        localProcessionUpperBound v <=
          divisorSource.localArithmeticUpperContribution
              localPrimeErrorContribution v -
            localMainLogContribution v

namespace IUTStage1IUTIVTheorem110LocalEstimateGateSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {divisorSource :
  IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate}

theorem localProcessionUpperBound_le_gap
    (source :
      IUTStage1IUTIVTheorem110LocalEstimateGateSource
        place divisorSource)
    (v : place) :
    source.localProcessionUpperBound v <=
      divisorSource.localArithmeticUpperContribution
          source.localPrimeErrorContribution v -
        source.localMainLogContribution v := by
  cases hkind : source.localKind v
  · exact source.stepV_distinguished_le_gap v hkind
  · exact source.stepVI_nondistinguished_le_gap v hkind
  · exact source.stepVII_archimedean_le_gap v hkind

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110LocalEstimateGateSource
        place divisorSource) :
    Prop :=
  (∀ v : place,
      0 <= source.localPrimeErrorContribution v) ∧
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ v : place, source.localPrimeErrorContribution v ∧
    estimate.mainLogTerm =
      ∑ v : place, source.localMainLogContribution v ∧
    (∀ v : place,
      source.localProcessionUpperBound v <=
        divisorSource.localArithmeticUpperContribution
            source.localPrimeErrorContribution v -
          source.localMainLogContribution v) ∧
    (∀ v : place,
      source.localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean ->
        source.localProcessionUpperBound v = 0)

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110LocalEstimateGateSource
        place divisorSource) :
    Endpoint source :=
  ⟨source.localPrimeErrorContribution_nonneg,
    source.primeErrorContribution_eq_sum,
    source.mainLogTerm_eq_sum,
    source.localProcessionUpperBound_le_gap,
    source.stepVI_nondistinguished_zero⟩

end IUTStage1IUTIVTheorem110LocalEstimateGateSource

set_option linter.style.longLine false in
/--
IUT IV, Theorem 1.10, Steps (v)--(vii), formula-level local source.

The older gate source stores an arbitrary `localProcessionUpperBound` together
with a proof for each case.  This stricter source defines that upper bound by
the paper's case split: a distinguished nonarchimedean displayed formula, zero
for nondistinguished nonarchimedean places, and an archimedean displayed
formula.  Thus the Step (vi) zero contribution is no longer supplied as a
separate payload; Lean derives it from the case distinction.
-/
structure IUTStage1IUTIVTheorem110LocalCaseFormulaSource
    (place : Type u) [Fintype place]
    {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
    (divisorSource :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate) where
  localKind : place -> IUTStage1IUTIVTheorem110LocalEstimateKind
  localPrimeErrorContribution : place -> Real
  localMainLogContribution : place -> Real
  distinguishedProcessionBound : place -> Real
  archimedeanProcessionBound : place -> Real
  localPrimeErrorContribution_nonneg :
    ∀ v : place, 0 <= localPrimeErrorContribution v
  primeErrorContribution_eq_sum :
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ v : place, localPrimeErrorContribution v
  mainLogTerm_eq_sum :
    estimate.mainLogTerm =
      ∑ v : place, localMainLogContribution v
  stepV_distinguished_formula_le_gap :
    ∀ v : place,
      localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
        distinguishedProcessionBound v <=
          divisorSource.localArithmeticUpperContribution
              localPrimeErrorContribution v -
            localMainLogContribution v
  stepVI_nondistinguished_gap_nonneg :
    ∀ v : place,
      localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean ->
        0 <=
          divisorSource.localArithmeticUpperContribution
              localPrimeErrorContribution v -
            localMainLogContribution v
  stepVII_archimedean_formula_le_gap :
    ∀ v : place,
      localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
        archimedeanProcessionBound v <=
          divisorSource.localArithmeticUpperContribution
              localPrimeErrorContribution v -
            localMainLogContribution v

namespace IUTStage1IUTIVTheorem110LocalCaseFormulaSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {divisorSource :
  IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate}

noncomputable def localProcessionUpperBound
    (source :
      IUTStage1IUTIVTheorem110LocalCaseFormulaSource
        place divisorSource)
    (v : place) :
    Real :=
  match source.localKind v with
  | IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean =>
      source.distinguishedProcessionBound v
  | IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean =>
      0
  | IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean =>
      source.archimedeanProcessionBound v

theorem localProcessionUpperBound_le_gap
    (source :
      IUTStage1IUTIVTheorem110LocalCaseFormulaSource
        place divisorSource)
    (v : place) :
    source.localProcessionUpperBound v <=
      divisorSource.localArithmeticUpperContribution
          source.localPrimeErrorContribution v -
        source.localMainLogContribution v := by
  cases hkind : source.localKind v
  · simpa [localProcessionUpperBound, hkind] using
      source.stepV_distinguished_formula_le_gap v hkind
  · simpa [localProcessionUpperBound, hkind] using
      source.stepVI_nondistinguished_gap_nonneg v hkind
  · simpa [localProcessionUpperBound, hkind] using
      source.stepVII_archimedean_formula_le_gap v hkind

theorem stepVI_nondistinguished_zero
    (source :
      IUTStage1IUTIVTheorem110LocalCaseFormulaSource
        place divisorSource)
    (v : place)
    (hkind :
      source.localKind v =
        IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean) :
    source.localProcessionUpperBound v = 0 := by
  simp [localProcessionUpperBound, hkind]

set_option linter.style.longLine false in
noncomputable def toLocalEstimateGateSource
    (source :
      IUTStage1IUTIVTheorem110LocalCaseFormulaSource
        place divisorSource) :
    IUTStage1IUTIVTheorem110LocalEstimateGateSource
      place divisorSource :=
  { localKind := source.localKind,
    localPrimeErrorContribution :=
      source.localPrimeErrorContribution,
    localMainLogContribution :=
      source.localMainLogContribution,
    localProcessionUpperBound :=
      source.localProcessionUpperBound,
    localPrimeErrorContribution_nonneg :=
      source.localPrimeErrorContribution_nonneg,
    primeErrorContribution_eq_sum :=
      source.primeErrorContribution_eq_sum,
    mainLogTerm_eq_sum :=
      source.mainLogTerm_eq_sum,
    stepV_distinguished_le_gap := by
      intro v hkind
      simpa [localProcessionUpperBound, hkind] using
        source.stepV_distinguished_formula_le_gap v hkind,
    stepVI_nondistinguished_zero := by
      intro v hkind
      exact source.stepVI_nondistinguished_zero v hkind,
    stepVI_nondistinguished_le_gap := by
      intro v hkind
      simpa [localProcessionUpperBound, hkind] using
        source.stepVI_nondistinguished_gap_nonneg v hkind,
    stepVII_archimedean_le_gap := by
      intro v hkind
      simpa [localProcessionUpperBound, hkind] using
        source.stepVII_archimedean_formula_le_gap v hkind }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110LocalCaseFormulaSource
        place divisorSource) :
    Prop :=
  (∀ v : place,
      0 <= source.localPrimeErrorContribution v) ∧
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ v : place, source.localPrimeErrorContribution v ∧
    estimate.mainLogTerm =
      ∑ v : place, source.localMainLogContribution v ∧
    (∀ v : place,
      source.localProcessionUpperBound v <=
        divisorSource.localArithmeticUpperContribution
            source.localPrimeErrorContribution v -
          source.localMainLogContribution v) ∧
    (∀ v : place,
      source.localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean ->
        source.localProcessionUpperBound v = 0) ∧
    IUTStage1IUTIVTheorem110LocalEstimateGateSource.Endpoint
      source.toLocalEstimateGateSource

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110LocalCaseFormulaSource
        place divisorSource) :
    Endpoint source :=
  ⟨source.localPrimeErrorContribution_nonneg,
    source.primeErrorContribution_eq_sum,
    source.mainLogTerm_eq_sum,
    source.localProcessionUpperBound_le_gap,
    source.stepVI_nondistinguished_zero,
    source.toLocalEstimateGateSource.endpoint⟩

end IUTStage1IUTIVTheorem110LocalCaseFormulaSource

set_option linter.style.longLine false in
/--
IUT IV, Theorem 1.10, Step (v), distinguished nonarchimedean local
log-shell estimate source.

This record is the Lean-facing trace of the passage
Proposition 1.4(iii) -> Proposition 1.7 weighted average -> Step (v)
procession-normalized bound.  The construction of the local valuation data and
the proof of the displayed Proposition 1.4 inclusion are still carried by the
source fields; the theorem below performs the ordered-real composition into the
Step (v) formula bound consumed by `IUTStage1IUTIVTheorem110LocalCaseFormulaSource`.
-/
structure IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate
    (_l : PrimeGeFive) (distinguishedProcessionBound : Real) where
  prop14ContainerUpperBound : Real
  weightedAverageUpperBound : Real
  exactProcessionNormalizedUpperBound : Real
  coarseProcessionNormalizedUpperBound : Real
  prop14_container_le_weighted_average :
    prop14ContainerUpperBound <= weightedAverageUpperBound
  proposition17_weighted_average_le_exact_procession :
    weightedAverageUpperBound <= exactProcessionNormalizedUpperBound
  stepV_exact_procession_le_coarse :
    exactProcessionNormalizedUpperBound <= coarseProcessionNormalizedUpperBound
  stepV_coarse_le_formula_bound :
    coarseProcessionNormalizedUpperBound <= distinguishedProcessionBound

namespace IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate

theorem prop14_container_le_formula_bound
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate
        l distinguishedProcessionBound) :
    source.prop14ContainerUpperBound <= distinguishedProcessionBound :=
  le_trans source.prop14_container_le_weighted_average
    (le_trans source.proposition17_weighted_average_le_exact_procession
      (le_trans source.stepV_exact_procession_le_coarse
        source.stepV_coarse_le_formula_bound))

theorem exact_procession_le_formula_bound
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate
        l distinguishedProcessionBound) :
    source.exactProcessionNormalizedUpperBound <=
      distinguishedProcessionBound :=
  le_trans source.stepV_exact_procession_le_coarse
    source.stepV_coarse_le_formula_bound

def Endpoint
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate
        l distinguishedProcessionBound) :
    Prop :=
  source.prop14ContainerUpperBound <= source.weightedAverageUpperBound ∧
    source.weightedAverageUpperBound <=
      source.exactProcessionNormalizedUpperBound ∧
      source.exactProcessionNormalizedUpperBound <=
        source.coarseProcessionNormalizedUpperBound ∧
        source.coarseProcessionNormalizedUpperBound <=
          distinguishedProcessionBound ∧
          source.prop14ContainerUpperBound <= distinguishedProcessionBound

theorem endpoint
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate
        l distinguishedProcessionBound) :
    Endpoint source :=
  ⟨source.prop14_container_le_weighted_average,
    source.proposition17_weighted_average_le_exact_procession,
    source.stepV_exact_procession_le_coarse,
    source.stepV_coarse_le_formula_bound,
    source.prop14_container_le_formula_bound⟩

end IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate

/--
IUT IV, Theorem 1.10, Step (vi), nondistinguished nonarchimedean local
log-shell estimate source.

Proposition 1.4(iv) gives the container `(R_I)^~` and log-volume `0`.  The
case-formula source already defines the nondistinguished procession bound to be
zero; this record supplies the remaining comparison of that zero value with the
local arithmetic-minus-main-log gap.
-/
structure IUTStage1IUTIVProposition14NondistinguishedLocalLogShellEstimate
    (localArithmeticMinusMainGap : Real) where
  tensorContainerLogVolume : Real
  prop14_tensor_container_logVolume_eq_zero :
    tensorContainerLogVolume = 0
  prop14_zero_le_gap :
    0 <= localArithmeticMinusMainGap

namespace IUTStage1IUTIVProposition14NondistinguishedLocalLogShellEstimate

theorem zero_le_gap
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedLocalLogShellEstimate
        localArithmeticMinusMainGap) :
    0 <= localArithmeticMinusMainGap :=
  source.prop14_zero_le_gap

def Endpoint
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedLocalLogShellEstimate
        localArithmeticMinusMainGap) :
    Prop :=
  source.tensorContainerLogVolume = 0 ∧
    0 <= localArithmeticMinusMainGap

theorem endpoint
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedLocalLogShellEstimate
        localArithmeticMinusMainGap) :
    Endpoint source :=
  ⟨source.prop14_tensor_container_logVolume_eq_zero,
    source.zero_le_gap⟩

end IUTStage1IUTIVProposition14NondistinguishedLocalLogShellEstimate

noncomputable def iutIVThetaPilotStepVIIArchimedeanExactBound
    (l : PrimeGeFive) (logPi : Real) : Real :=
  (((l.value : Real) + 5) / 4) * logPi

noncomputable def iutIVThetaPilotStepVIIArchimedeanCoarseBound
    (l : PrimeGeFive) : Real :=
  (((l.value : Real) + 1) / 4) * 4

theorem iutIVThetaPilotStepVIIArchimedeanExactBound_le_coarse
    (l : PrimeGeFive) {logPi : Real}
    (logPi_le_two : logPi <= 2) :
    iutIVThetaPilotStepVIIArchimedeanExactBound l logPi <=
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l := by
  have hl : (5 : Real) <= (l.value : Real) := by
    exact_mod_cast l.ge_five
  dsimp [iutIVThetaPilotStepVIIArchimedeanExactBound,
    iutIVThetaPilotStepVIIArchimedeanCoarseBound]
  nlinarith

set_option linter.style.longLine false in
/--
IUT IV, Theorem 1.10, Step (vii), archimedean metric estimate source.

Proposition 1.5(iii),(iv) supplies the invariant direct-sum integral structure
`B_I`, the `pi^(j+1) * B_I` container, and the `(j+1)log(pi)` local bound.
The theorem below performs the final Step (vii) coarse estimate
`((l+5)/4)log(pi) <= ((l+1)/4)*4` from `log(pi) <= 2` and `l >= 5`.
-/
structure IUTStage1IUTIVProposition15ArchimedeanLocalMetricEstimate
    (l : PrimeGeFive) (archimedeanProcessionBound : Real) where
  metricContainerLogVolume : Real
  logPi : Real
  prop15_container_le_exact_procession :
    metricContainerLogVolume <=
      iutIVThetaPilotStepVIIArchimedeanExactBound l logPi
  logPi_le_two : logPi <= 2
  stepVII_coarse_le_formula_bound :
    iutIVThetaPilotStepVIIArchimedeanCoarseBound l <=
      archimedeanProcessionBound

namespace IUTStage1IUTIVProposition15ArchimedeanLocalMetricEstimate

theorem exact_procession_le_coarse
    {l : PrimeGeFive} {archimedeanProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition15ArchimedeanLocalMetricEstimate
        l archimedeanProcessionBound) :
    iutIVThetaPilotStepVIIArchimedeanExactBound l source.logPi <=
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l :=
  iutIVThetaPilotStepVIIArchimedeanExactBound_le_coarse
    l source.logPi_le_two

theorem metric_container_le_formula_bound
    {l : PrimeGeFive} {archimedeanProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition15ArchimedeanLocalMetricEstimate
        l archimedeanProcessionBound) :
    source.metricContainerLogVolume <= archimedeanProcessionBound :=
  le_trans source.prop15_container_le_exact_procession
    (le_trans source.exact_procession_le_coarse
      source.stepVII_coarse_le_formula_bound)

def Endpoint
    {l : PrimeGeFive} {archimedeanProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition15ArchimedeanLocalMetricEstimate
        l archimedeanProcessionBound) :
    Prop :=
  source.metricContainerLogVolume <=
      iutIVThetaPilotStepVIIArchimedeanExactBound l source.logPi ∧
    iutIVThetaPilotStepVIIArchimedeanExactBound l source.logPi <=
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l ∧
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l <=
        archimedeanProcessionBound ∧
        source.metricContainerLogVolume <= archimedeanProcessionBound

theorem endpoint
    {l : PrimeGeFive} {archimedeanProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition15ArchimedeanLocalMetricEstimate
        l archimedeanProcessionBound) :
    Endpoint source :=
  ⟨source.prop15_container_le_exact_procession,
    source.exact_procession_le_coarse,
    source.stepVII_coarse_le_formula_bound,
    source.metric_container_le_formula_bound⟩

end IUTStage1IUTIVProposition15ArchimedeanLocalMetricEstimate

noncomputable def iutIVProp14DistinguishedLogUnitsFirstBound
    (residuePrime : Nat) (lambda dI : Real) (exceptionalCard : Nat) : Real :=
  -lambda + dI + 3 +
    4 * (exceptionalCard : Real) / (residuePrime : Real) *
      Real.log (residuePrime : Real)

noncomputable def iutIVProp14DistinguishedTensorBound
    (residuePrime : Nat) (lambda dI : Real)
    (exceptionalRamificationLogSum : Real) : Real :=
  -lambda + dI + 4 * Real.log (residuePrime : Real) +
    exceptionalRamificationLogSum

def IUTStage1IUTIVFiniteExtensionHaarCompactOpenLogVolumeEndpoint
    {α : Type u} {η : Type v} {K : Type w}
    {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
    (data :
      IUTStage1FiniteExtensionHaarCompactOpenLogVolumeSource
        α η K hullSystem) :
    Prop :=
  (∀ subset : Set K,
      data.realizedRegion subset = data.realization '' subset) ∧
    (∀ subset : Set K,
      data.normalizedHaarLogVolume subset =
        data.rawHaarLogVolume subset /
          (data.finiteExtensionDegree : Real)) ∧
    data.normalizedHaarLogVolume data.ringOfIntegers = 0 ∧
    data.normalizedHaarLogVolume data.uniformizerScaledSubset =
      data.normalizedHaarLogVolume data.compactOpenSubset -
        Real.log (data.residuePrime : Real) ∧
    (data.toNonarchimedeanLocalCompactOpenLogVolumeSource).compactOpenRegion =
      data.realizedRegion data.compactOpenSubset ∧
    (data.toNonarchimedeanLocalCompactOpenLogVolumeSource).normalizedLogVolume =
      data.normalizedHaarLogVolume data.compactOpenSubset ∧
    ((data.toNonarchimedeanLocalCompactOpenLogVolumeSource)
      |>.toLocalCompactOpenTensorFactorSource).compactOpenRegion =
      data.realizedRegion data.compactOpenSubset

theorem iutIVFiniteExtensionHaarCompactOpenLogVolumeEndpoint
    {α : Type u} {η : Type v} {K : Type w}
    {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
    (data :
      IUTStage1FiniteExtensionHaarCompactOpenLogVolumeSource
        α η K hullSystem) :
    IUTStage1IUTIVFiniteExtensionHaarCompactOpenLogVolumeEndpoint data :=
  data.endpoint

def IUTStage1IUTIVCompactOpenTopologyHaarNormalizationEndpoint
    {α : Type u} {η : Type v} {K : Type w}
    {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
    (data :
      IUTStage1FiniteExtensionCompactOpenTopologyHaarNormalizationSource
        α η K hullSystem) :
    Prop :=
  data.isCompactOpen data.ringOfIntegers ∧
    data.isCompactOpen data.compactOpenSubset ∧
    data.isCompactOpen data.uniformizerScaledSubset ∧
    data.rawHaarLogVolume data.compactOpenSubset =
      Real.log (data.rawHaarMeasure data.compactOpenSubset) ∧
    data.normalizedHaarLogVolume data.compactOpenSubset =
      data.rawHaarLogVolume data.compactOpenSubset /
        (data.finiteExtensionDegree : Real) ∧
    data.normalizedHaarLogVolume data.ringOfIntegers = 0 ∧
    data.normalizedHaarLogVolume data.uniformizerScaledSubset =
      data.normalizedHaarLogVolume data.compactOpenSubset -
        Real.log (data.residuePrime : Real) ∧
    (data.toFiniteExtensionHaarCompactOpenLogVolumeSource
      |>.toNonarchimedeanLocalCompactOpenLogVolumeSource).compactOpenRegion =
      data.realizedRegion data.compactOpenSubset

theorem iutIVCompactOpenTopologyHaarNormalizationEndpoint
    {α : Type u} {η : Type v} {K : Type w}
    {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
    (data :
      IUTStage1FiniteExtensionCompactOpenTopologyHaarNormalizationSource
        α η K hullSystem) :
    IUTStage1IUTIVCompactOpenTopologyHaarNormalizationEndpoint data :=
  data.endpoint

def IUTStage1IUTIVAdditiveHaarCompactOpenNormalizationEndpoint
    {α : Type u} {η : Type v} {K : Type w}
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
    (data :
      IUTStage1AdditiveHaarCompactOpenNormalizationSource
        α η K hullSystem) :
    Prop :=
  IsOpen data.ringOfIntegers ∧
    IsCompact data.ringOfIntegers ∧
    IsOpen data.compactOpenSubset ∧
    IsCompact data.compactOpenSubset ∧
    data.isCompactOpen data.uniformizerScaledSubset ∧
    data.rawHaarMeasure data.ringOfIntegers = 1 ∧
    0 < data.rawHaarMeasure data.compactOpenSubset ∧
    data.rawHaarLogVolume data.uniformizerScaledSubset =
      data.rawHaarLogVolume data.compactOpenSubset -
        (data.finiteExtensionDegree : Real) *
          Real.log (data.residuePrime : Real) ∧
    data.normalizedHaarLogVolume data.ringOfIntegers = 0 ∧
    data.normalizedHaarLogVolume data.uniformizerScaledSubset =
      data.normalizedHaarLogVolume data.compactOpenSubset -
        Real.log (data.residuePrime : Real) ∧
    (data.toCompactOpenTopologyHaarNormalizationSource
      |>.toFiniteExtensionHaarCompactOpenLogVolumeSource
      |>.toNonarchimedeanLocalCompactOpenLogVolumeSource).compactOpenRegion =
      data.realizedRegion data.compactOpenSubset

theorem iutIVAdditiveHaarCompactOpenNormalizationEndpoint
    {α : Type u} {η : Type v} {K : Type w}
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
    (data :
      IUTStage1AdditiveHaarCompactOpenNormalizationSource
        α η K hullSystem) :
    IUTStage1IUTIVAdditiveHaarCompactOpenNormalizationEndpoint data :=
  data.endpoint

set_option linter.style.longLine false in
/--
IUT IV, Proposition 1.4(i),(iii) construction source for the distinguished
nonarchimedean Step (v) estimate.

The finite-extension Haar source supplies the normalized log-volume convention
`mu_log(O_K)=0` and the uniformizer shift law from Proposition 1.4(i).  The
fields below then name the two displayed Proposition 1.4(iii) container bounds
and the Proposition 1.7 / Step (v) passage to the procession-normalized formula
bound.  Thus the downstream estimate record is no longer an arbitrary tuple of
four inequalities; it is constructed from paper-named local log-volume data.
-/
structure IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource
    (α : Type u) (η : Type v) (K : Type w)
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive) (distinguishedProcessionBound : Real) where
  finiteExtensionHaarSource :
    IUTStage1FiniteExtensionHaarCompactOpenLogVolumeSource
      α η K hullSystem
  lambda : Real
  dI : Real
  exceptionalCard : Nat
  exceptionalRamificationLogSum : Real
  shiftedLogUnitsRegion : Set α
  shiftedTensorRegion : Set α
  shiftedLogUnitsLogVolume : Real
  shiftedTensorLogVolume : Real
  shiftedLogUnits_logVolume_eq :
    shiftedLogUnitsLogVolume =
      hullSystem.logVolume shiftedLogUnitsRegion
  shiftedTensor_logVolume_eq :
    shiftedTensorLogVolume =
      hullSystem.logVolume shiftedTensorRegion
  prop14_logUnits_le_first_bound :
    shiftedLogUnitsLogVolume <=
      iutIVProp14DistinguishedLogUnitsFirstBound
        finiteExtensionHaarSource.residuePrime lambda dI exceptionalCard
  prop14_tensor_le_second_bound :
    shiftedTensorLogVolume <=
      iutIVProp14DistinguishedTensorBound
        finiteExtensionHaarSource.residuePrime lambda dI
        exceptionalRamificationLogSum
  prop14_first_bound_le_weighted_average :
    iutIVProp14DistinguishedLogUnitsFirstBound
        finiteExtensionHaarSource.residuePrime lambda dI exceptionalCard <=
      iutIVProp14DistinguishedTensorBound
        finiteExtensionHaarSource.residuePrime lambda dI
        exceptionalRamificationLogSum
  exactProcessionNormalizedUpperBound : Real
  coarseProcessionNormalizedUpperBound : Real
  proposition17_weighted_average_le_exact_procession :
    iutIVProp14DistinguishedTensorBound
        finiteExtensionHaarSource.residuePrime lambda dI
        exceptionalRamificationLogSum <=
      exactProcessionNormalizedUpperBound
  stepV_exact_procession_le_coarse :
    exactProcessionNormalizedUpperBound <=
      coarseProcessionNormalizedUpperBound
  stepV_coarse_le_formula_bound :
    coarseProcessionNormalizedUpperBound <= distinguishedProcessionBound

namespace IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource

variable {α : Type u} {η : Type v} {K : Type w}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}

noncomputable def firstBound
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource
        α η K hullSystem l distinguishedProcessionBound) :
    Real :=
  iutIVProp14DistinguishedLogUnitsFirstBound
    source.finiteExtensionHaarSource.residuePrime source.lambda source.dI
    source.exceptionalCard

noncomputable def tensorBound
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource
        α η K hullSystem l distinguishedProcessionBound) :
    Real :=
  iutIVProp14DistinguishedTensorBound
    source.finiteExtensionHaarSource.residuePrime source.lambda source.dI
    source.exceptionalRamificationLogSum

theorem shiftedLogUnits_le_tensorBound
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource
        α η K hullSystem l distinguishedProcessionBound) :
    source.shiftedLogUnitsLogVolume <= source.tensorBound :=
  le_trans source.prop14_logUnits_le_first_bound
    source.prop14_first_bound_le_weighted_average

set_option linter.style.longLine false in
noncomputable def toDistinguishedLocalLogShellEstimate
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource
        α η K hullSystem l distinguishedProcessionBound) :
    IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate
      l distinguishedProcessionBound :=
  { prop14ContainerUpperBound := source.shiftedLogUnitsLogVolume,
    weightedAverageUpperBound := source.tensorBound,
    exactProcessionNormalizedUpperBound :=
      source.exactProcessionNormalizedUpperBound,
    coarseProcessionNormalizedUpperBound :=
      source.coarseProcessionNormalizedUpperBound,
    prop14_container_le_weighted_average :=
      source.shiftedLogUnits_le_tensorBound,
    proposition17_weighted_average_le_exact_procession :=
      source.proposition17_weighted_average_le_exact_procession,
    stepV_exact_procession_le_coarse :=
      source.stepV_exact_procession_le_coarse,
    stepV_coarse_le_formula_bound :=
      source.stepV_coarse_le_formula_bound }

def Endpoint
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource
        α η K hullSystem l distinguishedProcessionBound) :
    Prop :=
  IUTStage1IUTIVFiniteExtensionHaarCompactOpenLogVolumeEndpoint
      source.finiteExtensionHaarSource ∧
    source.shiftedLogUnitsLogVolume =
      hullSystem.logVolume source.shiftedLogUnitsRegion ∧
    source.shiftedTensorLogVolume =
      hullSystem.logVolume source.shiftedTensorRegion ∧
    source.shiftedLogUnitsLogVolume <= source.firstBound ∧
    source.shiftedTensorLogVolume <= source.tensorBound ∧
    source.firstBound <= source.tensorBound ∧
    source.tensorBound <= source.exactProcessionNormalizedUpperBound ∧
    source.exactProcessionNormalizedUpperBound <=
      source.coarseProcessionNormalizedUpperBound ∧
    source.coarseProcessionNormalizedUpperBound <=
      distinguishedProcessionBound ∧
    source.toDistinguishedLocalLogShellEstimate.Endpoint

theorem endpoint
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource
        α η K hullSystem l distinguishedProcessionBound) :
    Endpoint source :=
  ⟨iutIVFiniteExtensionHaarCompactOpenLogVolumeEndpoint
      source.finiteExtensionHaarSource,
    source.shiftedLogUnits_logVolume_eq,
    source.shiftedTensor_logVolume_eq,
    source.prop14_logUnits_le_first_bound,
    source.prop14_tensor_le_second_bound,
    source.prop14_first_bound_le_weighted_average,
    source.proposition17_weighted_average_le_exact_procession,
    source.stepV_exact_procession_le_coarse,
    source.stepV_coarse_le_formula_bound,
    source.toDistinguishedLocalLogShellEstimate.endpoint⟩

end IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource

set_option linter.style.longLine false in
/--
IUT IV, Proposition 1.4(i),(iv) construction source for the nondistinguished
nonarchimedean Step (vi) estimate.

The lower Haar source supplies the normalized zero statement; the additional
fields identify the nondistinguished tensor container `(R_I)^~` with that
normalized integral container and keep the Proposition 1.2(iv) preservation
statement as an explicit source-paper proposition.
-/
structure IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource
    (α : Type u) (η : Type v) (K : Type w)
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (localArithmeticMinusMainGap : Real) where
  finiteExtensionHaarSource :
    IUTStage1FiniteExtensionHaarCompactOpenLogVolumeSource
      α η K hullSystem
  tensorContainerRegion : Set α
  tensorContainerLogVolume : Real
  tensorContainerRegion_eq_integralRegion :
    tensorContainerRegion =
      finiteExtensionHaarSource.realizedRegion
        finiteExtensionHaarSource.ringOfIntegers
  tensorContainerLogVolume_eq_hull :
    tensorContainerLogVolume =
      hullSystem.logVolume tensorContainerRegion
  prop14_phi_preserves_tensorContainer : Prop
  prop14_phi_preserves_tensorContainer_holds :
    prop14_phi_preserves_tensorContainer
  prop14_zero_le_gap :
    0 <= localArithmeticMinusMainGap

namespace IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource

variable {α : Type u} {η : Type v} {K : Type w}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}

theorem tensorContainerLogVolume_eq_zero
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource
        α η K hullSystem localArithmeticMinusMainGap) :
    source.tensorContainerLogVolume = 0 := by
  calc
    source.tensorContainerLogVolume =
        hullSystem.logVolume source.tensorContainerRegion :=
      source.tensorContainerLogVolume_eq_hull
    _ =
        hullSystem.logVolume
          (source.finiteExtensionHaarSource.realizedRegion
            source.finiteExtensionHaarSource.ringOfIntegers) := by
      rw [source.tensorContainerRegion_eq_integralRegion]
    _ =
        source.finiteExtensionHaarSource.normalizedHaarLogVolume
          source.finiteExtensionHaarSource.ringOfIntegers :=
      source.finiteExtensionHaarSource.hull_logVolume_eq_normalized
        source.finiteExtensionHaarSource.ringOfIntegers
    _ = 0 :=
      source.finiteExtensionHaarSource.ringOfIntegers_normalized_zero

noncomputable def toNondistinguishedLocalLogShellEstimate
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource
        α η K hullSystem localArithmeticMinusMainGap) :
    IUTStage1IUTIVProposition14NondistinguishedLocalLogShellEstimate
      localArithmeticMinusMainGap :=
  { tensorContainerLogVolume := source.tensorContainerLogVolume,
    prop14_tensor_container_logVolume_eq_zero :=
      source.tensorContainerLogVolume_eq_zero,
    prop14_zero_le_gap := source.prop14_zero_le_gap }

def Endpoint
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource
        α η K hullSystem localArithmeticMinusMainGap) :
    Prop :=
  IUTStage1IUTIVFiniteExtensionHaarCompactOpenLogVolumeEndpoint
      source.finiteExtensionHaarSource ∧
    source.tensorContainerRegion =
      source.finiteExtensionHaarSource.realizedRegion
        source.finiteExtensionHaarSource.ringOfIntegers ∧
    source.tensorContainerLogVolume =
      hullSystem.logVolume source.tensorContainerRegion ∧
    source.prop14_phi_preserves_tensorContainer ∧
    source.tensorContainerLogVolume = 0 ∧
    0 <= localArithmeticMinusMainGap ∧
    source.toNondistinguishedLocalLogShellEstimate.Endpoint

theorem endpoint
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource
        α η K hullSystem localArithmeticMinusMainGap) :
    Endpoint source :=
  ⟨iutIVFiniteExtensionHaarCompactOpenLogVolumeEndpoint
      source.finiteExtensionHaarSource,
    source.tensorContainerRegion_eq_integralRegion,
    source.tensorContainerLogVolume_eq_hull,
    source.prop14_phi_preserves_tensorContainer_holds,
    source.tensorContainerLogVolume_eq_zero,
    source.prop14_zero_le_gap,
    source.toNondistinguishedLocalLogShellEstimate.endpoint⟩

end IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource

set_option linter.style.longLine false in
/--
IUT IV, Proposition 1.4 distinguished source lowered to compact-open Haar
normalization.

This consumes the compact-open topology/Haar normalization source from the
Remark~3.9.5 local analytic stack and projects it to the finite-extension Haar
source used by the distinguished log-shell construction.
-/
structure IUTStage1IUTIVProposition14DistinguishedCompactOpenHaarLogShellSource
    (α : Type u) (η : Type v) (K : Type w)
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive) (distinguishedProcessionBound : Real) where
  compactOpenHaarSource :
    IUTStage1FiniteExtensionCompactOpenTopologyHaarNormalizationSource
      α η K hullSystem
  lambda : Real
  dI : Real
  exceptionalCard : Nat
  exceptionalRamificationLogSum : Real
  shiftedLogUnitsRegion : Set α
  shiftedTensorRegion : Set α
  shiftedLogUnitsLogVolume : Real
  shiftedTensorLogVolume : Real
  shiftedLogUnits_logVolume_eq :
    shiftedLogUnitsLogVolume =
      hullSystem.logVolume shiftedLogUnitsRegion
  shiftedTensor_logVolume_eq :
    shiftedTensorLogVolume =
      hullSystem.logVolume shiftedTensorRegion
  prop14_logUnits_le_first_bound :
    shiftedLogUnitsLogVolume <=
      iutIVProp14DistinguishedLogUnitsFirstBound
        compactOpenHaarSource.residuePrime lambda dI exceptionalCard
  prop14_tensor_le_second_bound :
    shiftedTensorLogVolume <=
      iutIVProp14DistinguishedTensorBound
        compactOpenHaarSource.residuePrime lambda dI
        exceptionalRamificationLogSum
  prop14_first_bound_le_weighted_average :
    iutIVProp14DistinguishedLogUnitsFirstBound
        compactOpenHaarSource.residuePrime lambda dI exceptionalCard <=
      iutIVProp14DistinguishedTensorBound
        compactOpenHaarSource.residuePrime lambda dI
        exceptionalRamificationLogSum
  exactProcessionNormalizedUpperBound : Real
  coarseProcessionNormalizedUpperBound : Real
  proposition17_weighted_average_le_exact_procession :
    iutIVProp14DistinguishedTensorBound
        compactOpenHaarSource.residuePrime lambda dI
        exceptionalRamificationLogSum <=
      exactProcessionNormalizedUpperBound
  stepV_exact_procession_le_coarse :
    exactProcessionNormalizedUpperBound <=
      coarseProcessionNormalizedUpperBound
  stepV_coarse_le_formula_bound :
    coarseProcessionNormalizedUpperBound <= distinguishedProcessionBound

namespace IUTStage1IUTIVProposition14DistinguishedCompactOpenHaarLogShellSource

variable {α : Type u} {η : Type v} {K : Type w}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}

set_option linter.style.longLine false in
noncomputable def toDistinguishedLocalLogShellConstructionSource
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedCompactOpenHaarLogShellSource
        α η K hullSystem l distinguishedProcessionBound) :
    IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource
      α η K hullSystem l distinguishedProcessionBound :=
  { finiteExtensionHaarSource :=
      source.compactOpenHaarSource
        |>.toFiniteExtensionHaarCompactOpenLogVolumeSource,
    lambda := source.lambda,
    dI := source.dI,
    exceptionalCard := source.exceptionalCard,
    exceptionalRamificationLogSum :=
      source.exceptionalRamificationLogSum,
    shiftedLogUnitsRegion := source.shiftedLogUnitsRegion,
    shiftedTensorRegion := source.shiftedTensorRegion,
    shiftedLogUnitsLogVolume := source.shiftedLogUnitsLogVolume,
    shiftedTensorLogVolume := source.shiftedTensorLogVolume,
    shiftedLogUnits_logVolume_eq :=
      source.shiftedLogUnits_logVolume_eq,
    shiftedTensor_logVolume_eq :=
      source.shiftedTensor_logVolume_eq,
    prop14_logUnits_le_first_bound :=
      source.prop14_logUnits_le_first_bound,
    prop14_tensor_le_second_bound :=
      source.prop14_tensor_le_second_bound,
    prop14_first_bound_le_weighted_average :=
      source.prop14_first_bound_le_weighted_average,
    exactProcessionNormalizedUpperBound :=
      source.exactProcessionNormalizedUpperBound,
    coarseProcessionNormalizedUpperBound :=
      source.coarseProcessionNormalizedUpperBound,
    proposition17_weighted_average_le_exact_procession :=
      source.proposition17_weighted_average_le_exact_procession,
    stepV_exact_procession_le_coarse :=
      source.stepV_exact_procession_le_coarse,
    stepV_coarse_le_formula_bound :=
      source.stepV_coarse_le_formula_bound }

def Endpoint
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedCompactOpenHaarLogShellSource
        α η K hullSystem l distinguishedProcessionBound) :
    Prop :=
  IUTStage1IUTIVCompactOpenTopologyHaarNormalizationEndpoint
      source.compactOpenHaarSource ∧
    source.toDistinguishedLocalLogShellConstructionSource.Endpoint

theorem endpoint
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedCompactOpenHaarLogShellSource
        α η K hullSystem l distinguishedProcessionBound) :
    Endpoint source :=
  ⟨iutIVCompactOpenTopologyHaarNormalizationEndpoint
      source.compactOpenHaarSource,
    source.toDistinguishedLocalLogShellConstructionSource.endpoint⟩

end IUTStage1IUTIVProposition14DistinguishedCompactOpenHaarLogShellSource

set_option linter.style.longLine false in
/--
IUT IV, Proposition 1.4 nondistinguished source lowered to compact-open Haar
normalization.
-/
structure IUTStage1IUTIVProposition14NondistinguishedCompactOpenHaarLogShellSource
    (α : Type u) (η : Type v) (K : Type w)
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (localArithmeticMinusMainGap : Real) where
  compactOpenHaarSource :
    IUTStage1FiniteExtensionCompactOpenTopologyHaarNormalizationSource
      α η K hullSystem
  tensorContainerRegion : Set α
  tensorContainerLogVolume : Real
  tensorContainerRegion_eq_integralRegion :
    tensorContainerRegion =
      compactOpenHaarSource.realizedRegion
        compactOpenHaarSource.ringOfIntegers
  tensorContainerLogVolume_eq_hull :
    tensorContainerLogVolume =
      hullSystem.logVolume tensorContainerRegion
  prop14_phi_preserves_tensorContainer : Prop
  prop14_phi_preserves_tensorContainer_holds :
    prop14_phi_preserves_tensorContainer
  prop14_zero_le_gap :
    0 <= localArithmeticMinusMainGap

namespace IUTStage1IUTIVProposition14NondistinguishedCompactOpenHaarLogShellSource

variable {α : Type u} {η : Type v} {K : Type w}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}

set_option linter.style.longLine false in
noncomputable def toNondistinguishedLocalLogShellConstructionSource
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedCompactOpenHaarLogShellSource
        α η K hullSystem localArithmeticMinusMainGap) :
    IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource
      α η K hullSystem localArithmeticMinusMainGap :=
  { finiteExtensionHaarSource :=
      source.compactOpenHaarSource
        |>.toFiniteExtensionHaarCompactOpenLogVolumeSource,
    tensorContainerRegion := source.tensorContainerRegion,
    tensorContainerLogVolume := source.tensorContainerLogVolume,
    tensorContainerRegion_eq_integralRegion :=
      source.tensorContainerRegion_eq_integralRegion,
    tensorContainerLogVolume_eq_hull :=
      source.tensorContainerLogVolume_eq_hull,
    prop14_phi_preserves_tensorContainer :=
      source.prop14_phi_preserves_tensorContainer,
    prop14_phi_preserves_tensorContainer_holds :=
      source.prop14_phi_preserves_tensorContainer_holds,
    prop14_zero_le_gap := source.prop14_zero_le_gap }

def Endpoint
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedCompactOpenHaarLogShellSource
        α η K hullSystem localArithmeticMinusMainGap) :
    Prop :=
  IUTStage1IUTIVCompactOpenTopologyHaarNormalizationEndpoint
      source.compactOpenHaarSource ∧
    source.toNondistinguishedLocalLogShellConstructionSource.Endpoint

theorem endpoint
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedCompactOpenHaarLogShellSource
        α η K hullSystem localArithmeticMinusMainGap) :
    Endpoint source :=
  ⟨iutIVCompactOpenTopologyHaarNormalizationEndpoint
      source.compactOpenHaarSource,
    source.toNondistinguishedLocalLogShellConstructionSource.endpoint⟩

end IUTStage1IUTIVProposition14NondistinguishedCompactOpenHaarLogShellSource

set_option linter.style.longLine false in
/--
IUT IV, Proposition 1.4 distinguished source lowered to additive Haar measure.

The additive Haar source derives the normalized log-volume zero and
uniformizer-shift law from a mathlib additive Haar measure plus the local
finite-extension normalization inputs.
-/
structure IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive) (distinguishedProcessionBound : Real) where
  additiveHaarSource :
    IUTStage1AdditiveHaarCompactOpenNormalizationSource
      α η K hullSystem
  lambda : Real
  dI : Real
  exceptionalCard : Nat
  exceptionalRamificationLogSum : Real
  shiftedLogUnitsRegion : Set α
  shiftedTensorRegion : Set α
  shiftedLogUnitsLogVolume : Real
  shiftedTensorLogVolume : Real
  shiftedLogUnits_logVolume_eq :
    shiftedLogUnitsLogVolume =
      hullSystem.logVolume shiftedLogUnitsRegion
  shiftedTensor_logVolume_eq :
    shiftedTensorLogVolume =
      hullSystem.logVolume shiftedTensorRegion
  prop14_logUnits_le_first_bound :
    shiftedLogUnitsLogVolume <=
      iutIVProp14DistinguishedLogUnitsFirstBound
        additiveHaarSource.residuePrime lambda dI exceptionalCard
  prop14_tensor_le_second_bound :
    shiftedTensorLogVolume <=
      iutIVProp14DistinguishedTensorBound
        additiveHaarSource.residuePrime lambda dI
        exceptionalRamificationLogSum
  prop14_first_bound_le_weighted_average :
    iutIVProp14DistinguishedLogUnitsFirstBound
        additiveHaarSource.residuePrime lambda dI exceptionalCard <=
      iutIVProp14DistinguishedTensorBound
        additiveHaarSource.residuePrime lambda dI
        exceptionalRamificationLogSum
  exactProcessionNormalizedUpperBound : Real
  coarseProcessionNormalizedUpperBound : Real
  proposition17_weighted_average_le_exact_procession :
    iutIVProp14DistinguishedTensorBound
        additiveHaarSource.residuePrime lambda dI
        exceptionalRamificationLogSum <=
      exactProcessionNormalizedUpperBound
  stepV_exact_procession_le_coarse :
    exactProcessionNormalizedUpperBound <=
      coarseProcessionNormalizedUpperBound
  stepV_coarse_le_formula_bound :
    coarseProcessionNormalizedUpperBound <= distinguishedProcessionBound

namespace IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}

set_option linter.style.longLine false in
noncomputable def toCompactOpenHaarLogShellSource
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
        α η K hullSystem l distinguishedProcessionBound) :
    IUTStage1IUTIVProposition14DistinguishedCompactOpenHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound :=
  { compactOpenHaarSource :=
      source.additiveHaarSource
        |>.toCompactOpenTopologyHaarNormalizationSource,
    lambda := source.lambda,
    dI := source.dI,
    exceptionalCard := source.exceptionalCard,
    exceptionalRamificationLogSum :=
      source.exceptionalRamificationLogSum,
    shiftedLogUnitsRegion := source.shiftedLogUnitsRegion,
    shiftedTensorRegion := source.shiftedTensorRegion,
    shiftedLogUnitsLogVolume := source.shiftedLogUnitsLogVolume,
    shiftedTensorLogVolume := source.shiftedTensorLogVolume,
    shiftedLogUnits_logVolume_eq :=
      source.shiftedLogUnits_logVolume_eq,
    shiftedTensor_logVolume_eq :=
      source.shiftedTensor_logVolume_eq,
    prop14_logUnits_le_first_bound :=
      source.prop14_logUnits_le_first_bound,
    prop14_tensor_le_second_bound :=
      source.prop14_tensor_le_second_bound,
    prop14_first_bound_le_weighted_average :=
      source.prop14_first_bound_le_weighted_average,
    exactProcessionNormalizedUpperBound :=
      source.exactProcessionNormalizedUpperBound,
    coarseProcessionNormalizedUpperBound :=
      source.coarseProcessionNormalizedUpperBound,
    proposition17_weighted_average_le_exact_procession :=
      source.proposition17_weighted_average_le_exact_procession,
    stepV_exact_procession_le_coarse :=
      source.stepV_exact_procession_le_coarse,
    stepV_coarse_le_formula_bound :=
      source.stepV_coarse_le_formula_bound }

noncomputable def toDistinguishedLocalLogShellConstructionSource
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
        α η K hullSystem l distinguishedProcessionBound) :
    IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource
      α η K hullSystem l distinguishedProcessionBound :=
  source.toCompactOpenHaarLogShellSource
    |>.toDistinguishedLocalLogShellConstructionSource

def Endpoint
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
        α η K hullSystem l distinguishedProcessionBound) :
    Prop :=
  IUTStage1IUTIVAdditiveHaarCompactOpenNormalizationEndpoint
      source.additiveHaarSource ∧
    source.toCompactOpenHaarLogShellSource.Endpoint ∧
    source.toDistinguishedLocalLogShellConstructionSource.Endpoint

theorem endpoint
    {l : PrimeGeFive} {distinguishedProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
        α η K hullSystem l distinguishedProcessionBound) :
    Endpoint source :=
  ⟨iutIVAdditiveHaarCompactOpenNormalizationEndpoint
      source.additiveHaarSource,
    source.toCompactOpenHaarLogShellSource.endpoint,
    source.toDistinguishedLocalLogShellConstructionSource.endpoint⟩

end IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource

set_option linter.style.longLine false in
/-- IUT IV, Proposition 1.4 nondistinguished source lowered to additive Haar measure. -/
structure IUTStage1IUTIVProposition14NondistinguishedAdditiveHaarLogShellSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (localArithmeticMinusMainGap : Real) where
  additiveHaarSource :
    IUTStage1AdditiveHaarCompactOpenNormalizationSource
      α η K hullSystem
  tensorContainerRegion : Set α
  tensorContainerLogVolume : Real
  tensorContainerRegion_eq_integralRegion :
    tensorContainerRegion =
      additiveHaarSource.realizedRegion additiveHaarSource.ringOfIntegers
  tensorContainerLogVolume_eq_hull :
    tensorContainerLogVolume =
      hullSystem.logVolume tensorContainerRegion
  prop14_phi_preserves_tensorContainer : Prop
  prop14_phi_preserves_tensorContainer_holds :
    prop14_phi_preserves_tensorContainer
  prop14_zero_le_gap :
    0 <= localArithmeticMinusMainGap

namespace IUTStage1IUTIVProposition14NondistinguishedAdditiveHaarLogShellSource

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}

set_option linter.style.longLine false in
noncomputable def toCompactOpenHaarLogShellSource
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedAdditiveHaarLogShellSource
        α η K hullSystem localArithmeticMinusMainGap) :
    IUTStage1IUTIVProposition14NondistinguishedCompactOpenHaarLogShellSource
      α η K hullSystem localArithmeticMinusMainGap :=
  { compactOpenHaarSource :=
      source.additiveHaarSource
        |>.toCompactOpenTopologyHaarNormalizationSource,
    tensorContainerRegion := source.tensorContainerRegion,
    tensorContainerLogVolume := source.tensorContainerLogVolume,
    tensorContainerRegion_eq_integralRegion :=
      source.tensorContainerRegion_eq_integralRegion,
    tensorContainerLogVolume_eq_hull :=
      source.tensorContainerLogVolume_eq_hull,
    prop14_phi_preserves_tensorContainer :=
      source.prop14_phi_preserves_tensorContainer,
    prop14_phi_preserves_tensorContainer_holds :=
      source.prop14_phi_preserves_tensorContainer_holds,
    prop14_zero_le_gap := source.prop14_zero_le_gap }

noncomputable def toNondistinguishedLocalLogShellConstructionSource
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedAdditiveHaarLogShellSource
        α η K hullSystem localArithmeticMinusMainGap) :
    IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource
      α η K hullSystem localArithmeticMinusMainGap :=
  source.toCompactOpenHaarLogShellSource
    |>.toNondistinguishedLocalLogShellConstructionSource

def Endpoint
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedAdditiveHaarLogShellSource
        α η K hullSystem localArithmeticMinusMainGap) :
    Prop :=
  IUTStage1IUTIVAdditiveHaarCompactOpenNormalizationEndpoint
      source.additiveHaarSource ∧
    source.toCompactOpenHaarLogShellSource.Endpoint ∧
    source.toNondistinguishedLocalLogShellConstructionSource.Endpoint

theorem endpoint
    {localArithmeticMinusMainGap : Real}
    (source :
      IUTStage1IUTIVProposition14NondistinguishedAdditiveHaarLogShellSource
        α η K hullSystem localArithmeticMinusMainGap) :
    Endpoint source :=
  ⟨iutIVAdditiveHaarCompactOpenNormalizationEndpoint
      source.additiveHaarSource,
    source.toCompactOpenHaarLogShellSource.endpoint,
    source.toNondistinguishedLocalLogShellConstructionSource.endpoint⟩

end IUTStage1IUTIVProposition14NondistinguishedAdditiveHaarLogShellSource

noncomputable def iutIVProp15ArchimedeanDirectSummandCount
    (I V : Type u) [Fintype I] [Fintype V] : Nat :=
  2 ^ (Fintype.card I - 1) * (Fintype.card V) ^ (Fintype.card I)

set_option linter.style.longLine false in
/--
IUT IV, Proposition 1.5(iii),(iv) construction source for the archimedean
Step (vii) metric estimate.

This source names the finite sets `I` and `V`, the direct-sum decomposition
cardinality `2^{|I|-1}|V|^{|I|}`, preservation under primitive automorphisms,
and the vector-length containment in `lambda^{|I|} B_I`.  The existing
archimedean estimate record is then obtained by projecting these metric data to
the exact `(l+5)/4 * log(pi)` bound and Lean's elementary exact-to-coarse
comparison.
-/
structure IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
    (I V : Type u) [Fintype I] [Fintype V]
    (l : PrimeGeFive) (archimedeanProcessionBound : Real) where
  I_nonempty : Nonempty I
  V_nonempty : Nonempty V
  directSummandCount : Nat
  directSummandCount_eq :
    directSummandCount =
      iutIVProp15ArchimedeanDirectSummandCount I V
  tensorProductMetric : Prop
  directSumMetric : Prop
  directSumMetric_scales_tensorProductMetric :
    directSumMetric
  integralStructurePreservedByPrimitiveAutomorphisms : Prop
  integralStructurePreserved :
    integralStructurePreservedByPrimitiveAutomorphisms
  tensorProductVectorsInScaledIntegralStructure : Prop
  tensorProductVectors_mem_scaledIntegralStructure :
    tensorProductVectorsInScaledIntegralStructure
  metricContainerLogVolume : Real
  logPi : Real
  prop15_container_le_exact_procession :
    metricContainerLogVolume <=
      iutIVThetaPilotStepVIIArchimedeanExactBound l logPi
  logPi_le_two : logPi <= 2
  stepVII_coarse_le_formula_bound :
    iutIVThetaPilotStepVIIArchimedeanCoarseBound l <=
      archimedeanProcessionBound

namespace IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource

variable {I V : Type u} [Fintype I] [Fintype V]

noncomputable def toArchimedeanLocalMetricEstimate
    {l : PrimeGeFive} {archimedeanProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
        I V l archimedeanProcessionBound) :
    IUTStage1IUTIVProposition15ArchimedeanLocalMetricEstimate
      l archimedeanProcessionBound :=
  { metricContainerLogVolume := source.metricContainerLogVolume,
    logPi := source.logPi,
    prop15_container_le_exact_procession :=
      source.prop15_container_le_exact_procession,
    logPi_le_two := source.logPi_le_two,
    stepVII_coarse_le_formula_bound :=
      source.stepVII_coarse_le_formula_bound }

def Endpoint
    {l : PrimeGeFive} {archimedeanProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
        I V l archimedeanProcessionBound) :
    Prop :=
  Nonempty I ∧
    Nonempty V ∧
    source.directSummandCount =
      iutIVProp15ArchimedeanDirectSummandCount I V ∧
    source.directSumMetric ∧
    source.integralStructurePreservedByPrimitiveAutomorphisms ∧
    source.tensorProductVectorsInScaledIntegralStructure ∧
    source.toArchimedeanLocalMetricEstimate.Endpoint

theorem endpoint
    {l : PrimeGeFive} {archimedeanProcessionBound : Real}
    (source :
      IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
        I V l archimedeanProcessionBound) :
    Endpoint source :=
  ⟨source.I_nonempty,
    source.V_nonempty,
    source.directSummandCount_eq,
    source.directSumMetric_scales_tensorProductMetric,
    source.integralStructurePreserved,
    source.tensorProductVectors_mem_scaledIntegralStructure,
    source.toArchimedeanLocalMetricEstimate.endpoint⟩

end IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource

set_option linter.style.longLine false in
/--
IUT IV, Theorem 1.10 local formula source backed by Proposition 1.4 and
Proposition 1.5 local estimates.

This is stricter than `IUTStage1IUTIVTheorem110LocalCaseFormulaSource`: the
Step (v), Step (vi), and Step (vii) inequalities are projected from
Proposition 1.4/1.5 estimate objects.  It is still a source boundary: the
valuation/log-shell constructions that instantiate these proposition objects
remain upstream obligations.
-/
structure IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource
    (place : Type u) [Fintype place]
    {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
    (divisorSource :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate) where
  localKind : place -> IUTStage1IUTIVTheorem110LocalEstimateKind
  localPrimeErrorContribution : place -> Real
  localMainLogContribution : place -> Real
  distinguishedProcessionBound : place -> Real
  archimedeanProcessionBound : place -> Real
  localPrimeErrorContribution_nonneg :
    ∀ v : place, 0 <= localPrimeErrorContribution v
  primeErrorContribution_eq_sum :
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ v : place, localPrimeErrorContribution v
  mainLogTerm_eq_sum :
    estimate.mainLogTerm =
      ∑ v : place, localMainLogContribution v
  distinguishedLogShellEstimate :
    ∀ v : place,
      localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
        IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate
          estimate.l (distinguishedProcessionBound v)
  nondistinguishedLogShellEstimate :
    ∀ v : place,
      localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean ->
        IUTStage1IUTIVProposition14NondistinguishedLocalLogShellEstimate
          (divisorSource.localArithmeticUpperContribution
              localPrimeErrorContribution v -
            localMainLogContribution v)
  archimedeanMetricEstimate :
    ∀ v : place,
      localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
        IUTStage1IUTIVProposition15ArchimedeanLocalMetricEstimate
          estimate.l (archimedeanProcessionBound v)

namespace IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {divisorSource :
  IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate}

theorem stepV_distinguished_formula_le_gap
    (source :
      IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource
        place divisorSource)
    (v : place)
    (_hkind :
      source.localKind v =
        IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean)
    (formula_le_gap :
      source.distinguishedProcessionBound v <=
        divisorSource.localArithmeticUpperContribution
            source.localPrimeErrorContribution v -
          source.localMainLogContribution v) :
    source.distinguishedProcessionBound v <=
      divisorSource.localArithmeticUpperContribution
          source.localPrimeErrorContribution v -
        source.localMainLogContribution v :=
  formula_le_gap

theorem stepVI_nondistinguished_gap_nonneg
    (source :
      IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource
        place divisorSource)
    (v : place)
    (hkind :
      source.localKind v =
        IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean) :
    0 <=
      divisorSource.localArithmeticUpperContribution
          source.localPrimeErrorContribution v -
        source.localMainLogContribution v :=
  (source.nondistinguishedLogShellEstimate v hkind).zero_le_gap

theorem stepVII_archimedean_formula_le_gap
    (source :
      IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource
        place divisorSource)
    (v : place)
    (_hkind :
      source.localKind v =
        IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean)
    (formula_le_gap :
      source.archimedeanProcessionBound v <=
        divisorSource.localArithmeticUpperContribution
            source.localPrimeErrorContribution v -
          source.localMainLogContribution v) :
    source.archimedeanProcessionBound v <=
      divisorSource.localArithmeticUpperContribution
          source.localPrimeErrorContribution v -
        source.localMainLogContribution v :=
  formula_le_gap

set_option linter.style.longLine false in
noncomputable def toLocalCaseFormulaSource
    (source :
      IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource
        place divisorSource)
    (distinguished_formula_le_gap :
      ∀ v : place,
        source.localKind v =
            IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
          source.distinguishedProcessionBound v <=
            divisorSource.localArithmeticUpperContribution
                source.localPrimeErrorContribution v -
              source.localMainLogContribution v)
    (archimedean_formula_le_gap :
      ∀ v : place,
        source.localKind v =
            IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
          source.archimedeanProcessionBound v <=
            divisorSource.localArithmeticUpperContribution
                source.localPrimeErrorContribution v -
              source.localMainLogContribution v) :
    IUTStage1IUTIVTheorem110LocalCaseFormulaSource
      place divisorSource :=
  { localKind := source.localKind,
    localPrimeErrorContribution :=
      source.localPrimeErrorContribution,
    localMainLogContribution :=
      source.localMainLogContribution,
    distinguishedProcessionBound :=
      source.distinguishedProcessionBound,
    archimedeanProcessionBound :=
      source.archimedeanProcessionBound,
    localPrimeErrorContribution_nonneg :=
      source.localPrimeErrorContribution_nonneg,
    primeErrorContribution_eq_sum :=
      source.primeErrorContribution_eq_sum,
    mainLogTerm_eq_sum :=
      source.mainLogTerm_eq_sum,
    stepV_distinguished_formula_le_gap :=
      distinguished_formula_le_gap,
    stepVI_nondistinguished_gap_nonneg :=
      source.stepVI_nondistinguished_gap_nonneg,
    stepVII_archimedean_formula_le_gap :=
      archimedean_formula_le_gap }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource
        place divisorSource) :
    Prop :=
  (∀ v : place,
      0 <= source.localPrimeErrorContribution v) ∧
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ v : place, source.localPrimeErrorContribution v ∧
    estimate.mainLogTerm =
      ∑ v : place, source.localMainLogContribution v ∧
    (∀ v : place,
      source.localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean ->
        0 <=
          divisorSource.localArithmeticUpperContribution
              source.localPrimeErrorContribution v -
            source.localMainLogContribution v) ∧
    (∀ v : place,
      (hkind :
        source.localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        (source.distinguishedLogShellEstimate v hkind).Endpoint) ∧
      (∀ v : place,
        (hkind :
          source.localKind v =
            IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean) ->
          (source.nondistinguishedLogShellEstimate v hkind).Endpoint) ∧
        (∀ v : place,
          (hkind :
            source.localKind v =
              IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
            (source.archimedeanMetricEstimate v hkind).Endpoint)

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource
        place divisorSource) :
    Endpoint source :=
  ⟨source.localPrimeErrorContribution_nonneg,
    source.primeErrorContribution_eq_sum,
    source.mainLogTerm_eq_sum,
    source.stepVI_nondistinguished_gap_nonneg,
    (fun v hkind => (source.distinguishedLogShellEstimate v hkind).endpoint),
    (fun v hkind => (source.nondistinguishedLogShellEstimate v hkind).endpoint),
    (fun v hkind => (source.archimedeanMetricEstimate v hkind).endpoint)⟩

set_option linter.style.longLine false in
/--
Endpoint preservation for the Proposition~1.4/1.5-backed local formula
projection.

Once the distinguished and archimedean procession formula bounds are compared
with the local arithmetic-minus-main-log gaps, the source projected from
Proposition~1.4/1.5 data satisfies the older Theorem~1.10 local-case formula
endpoint.  This names the exact handoff from paper-level local estimates to the
local-case source consumed by the arithmetic-divisor evaluation layer.
-/
theorem toLocalCaseFormulaSource_endpoint
    (source :
      IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource
        place divisorSource)
    (distinguished_formula_le_gap :
      ∀ v : place,
        source.localKind v =
            IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
          source.distinguishedProcessionBound v <=
            divisorSource.localArithmeticUpperContribution
                source.localPrimeErrorContribution v -
              source.localMainLogContribution v)
    (archimedean_formula_le_gap :
      ∀ v : place,
        source.localKind v =
            IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
          source.archimedeanProcessionBound v <=
            divisorSource.localArithmeticUpperContribution
                source.localPrimeErrorContribution v -
              source.localMainLogContribution v) :
    (source.toLocalCaseFormulaSource
      distinguished_formula_le_gap archimedean_formula_le_gap).Endpoint :=
  (source.toLocalCaseFormulaSource
    distinguished_formula_le_gap archimedean_formula_le_gap).endpoint

end IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource

set_option linter.style.longLine false in
/--
Constructor layer from IUT IV arithmetic divisors plus Theorem 1.10 local
estimate gates to the older real-valued local evaluation source.
-/
structure IUTStage1IUTIVTheorem110ArithmeticDivisorEvaluationSource
    (place : Type u) [Fintype place]
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) where
  arithmeticDivisorSource :
    IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate
  localEstimateGateSource :
    IUTStage1IUTIVTheorem110LocalEstimateGateSource
      place arithmeticDivisorSource

namespace IUTStage1IUTIVTheorem110ArithmeticDivisorEvaluationSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}

set_option linter.style.longLine false in
noncomputable def toThetaPilotArithmeticDivisorLocalEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorEvaluationSource
        place estimate) :
    IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
      place estimate :=
  { localDifferentDegree :=
      source.arithmeticDivisorSource.localDifferentDegree,
    localConductorDegree :=
      source.arithmeticDivisorSource.localConductorDegree,
    localPrimeErrorContribution :=
      source.localEstimateGateSource.localPrimeErrorContribution,
    localMainLogContribution :=
      source.localEstimateGateSource.localMainLogContribution,
    localDifferentDegree_nonneg :=
      source.arithmeticDivisorSource.localDifferentDegree_nonneg,
    localConductorDegree_nonneg :=
      source.arithmeticDivisorSource.localConductorDegree_nonneg,
    localPrimeErrorContribution_nonneg :=
      source.localEstimateGateSource.localPrimeErrorContribution_nonneg,
    logDifferentFtpd_eq_sum :=
      source.arithmeticDivisorSource.logDifferentFtpd_eq_sum,
    logConductorFtpd_eq_sum :=
      source.arithmeticDivisorSource.logConductorFtpd_eq_sum,
    primeErrorContribution_eq_sum :=
      source.localEstimateGateSource.primeErrorContribution_eq_sum,
    mainLogTerm_eq_sum :=
      source.localEstimateGateSource.mainLogTerm_eq_sum }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorEvaluationSource
        place estimate) :
    Prop :=
  source.arithmeticDivisorSource.Endpoint ∧
    source.localEstimateGateSource.Endpoint ∧
      IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource.Endpoint
        source.toThetaPilotArithmeticDivisorLocalEvaluationSource

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorEvaluationSource
        place estimate) :
    Endpoint source :=
  ⟨source.arithmeticDivisorSource.endpoint,
    source.localEstimateGateSource.endpoint,
    source.toThetaPilotArithmeticDivisorLocalEvaluationSource.endpoint⟩

theorem localProcessionUpperBound_le_gap
    (source :
      IUTStage1IUTIVTheorem110ArithmeticDivisorEvaluationSource
        place estimate)
    (v : place) :
    source.localEstimateGateSource.localProcessionUpperBound v <=
      source.arithmeticDivisorSource.localArithmeticUpperContribution
          source.localEstimateGateSource.localPrimeErrorContribution v -
        source.localEstimateGateSource.localMainLogContribution v :=
  source.localEstimateGateSource.localProcessionUpperBound_le_gap v

end IUTStage1IUTIVTheorem110ArithmeticDivisorEvaluationSource

set_option linter.style.longLine false in
/--
Constructor layer from arithmetic divisors plus the formula-level Step
(v)--(vii) source.

This is the preferred local Theorem 1.10 source boundary: the local evaluation
source is obtained from typed arithmetic divisors and a case-defined procession
upper bound, before projecting to the older gate/evaluation records.
-/
structure IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource
    (place : Type u) [Fintype place]
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) where
  arithmeticDivisorSource :
    IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate
  localCaseFormulaSource :
    IUTStage1IUTIVTheorem110LocalCaseFormulaSource
      place arithmeticDivisorSource

namespace IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}

noncomputable def toTheorem110ArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource
        place estimate) :
    IUTStage1IUTIVTheorem110ArithmeticDivisorEvaluationSource
      place estimate :=
  { arithmeticDivisorSource := source.arithmeticDivisorSource,
    localEstimateGateSource :=
      source.localCaseFormulaSource.toLocalEstimateGateSource }

noncomputable def toThetaPilotArithmeticDivisorLocalEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource
        place estimate) :
    IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
      place estimate :=
  source.toTheorem110ArithmeticDivisorEvaluationSource
    |>.toThetaPilotArithmeticDivisorLocalEvaluationSource

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource
        place estimate) :
    Prop :=
  source.arithmeticDivisorSource.Endpoint ∧
    source.localCaseFormulaSource.Endpoint ∧
      IUTStage1IUTIVTheorem110ArithmeticDivisorEvaluationSource.Endpoint
        source.toTheorem110ArithmeticDivisorEvaluationSource ∧
        IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource.Endpoint
          source.toThetaPilotArithmeticDivisorLocalEvaluationSource

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource
        place estimate) :
    Endpoint source :=
  ⟨source.arithmeticDivisorSource.endpoint,
    source.localCaseFormulaSource.endpoint,
    source.toTheorem110ArithmeticDivisorEvaluationSource.endpoint,
    source.toThetaPilotArithmeticDivisorLocalEvaluationSource.endpoint⟩

theorem localProcessionUpperBound_le_gap
    (source :
      IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource
        place estimate)
    (v : place) :
    source.localCaseFormulaSource.localProcessionUpperBound v <=
      source.arithmeticDivisorSource.localArithmeticUpperContribution
          source.localCaseFormulaSource.localPrimeErrorContribution v -
        source.localCaseFormulaSource.localMainLogContribution v :=
  source.localCaseFormulaSource.localProcessionUpperBound_le_gap v

end IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource

set_option linter.style.longLine false in
/--
Constructor layer from arithmetic divisors plus Proposition 1.4/1.5-backed
local log-shell estimates.

The distinguished and archimedean formula-to-gap comparisons are kept as the
remaining Step~(xi)/IUT IV matching payload.  The nondistinguished gap is
derived from the Proposition 1.4(iv) source object.
-/
structure IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource
    (place : Type u) [Fintype place]
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow) where
  arithmeticDivisorSource :
    IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate
  propositionLogShellFormulaSource :
    IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource
      place arithmeticDivisorSource
  distinguished_formula_le_gap :
    ∀ v : place,
      propositionLogShellFormulaSource.localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
        propositionLogShellFormulaSource.distinguishedProcessionBound v <=
          arithmeticDivisorSource.localArithmeticUpperContribution
              propositionLogShellFormulaSource.localPrimeErrorContribution v -
            propositionLogShellFormulaSource.localMainLogContribution v
  archimedean_formula_le_gap :
    ∀ v : place,
      propositionLogShellFormulaSource.localKind v =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
        propositionLogShellFormulaSource.archimedeanProcessionBound v <=
          arithmeticDivisorSource.localArithmeticUpperContribution
              propositionLogShellFormulaSource.localPrimeErrorContribution v -
            propositionLogShellFormulaSource.localMainLogContribution v

namespace IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}

noncomputable def toFormulaArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource
        place estimate) :
    IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource
      place estimate :=
  { arithmeticDivisorSource := source.arithmeticDivisorSource,
    localCaseFormulaSource :=
      source.propositionLogShellFormulaSource.toLocalCaseFormulaSource
        source.distinguished_formula_le_gap
        source.archimedean_formula_le_gap }

noncomputable def toTheorem110ArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource
        place estimate) :
    IUTStage1IUTIVTheorem110ArithmeticDivisorEvaluationSource
      place estimate :=
  source.toFormulaArithmeticDivisorEvaluationSource
    |>.toTheorem110ArithmeticDivisorEvaluationSource

noncomputable def toThetaPilotArithmeticDivisorLocalEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource
        place estimate) :
    IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
      place estimate :=
  source.toFormulaArithmeticDivisorEvaluationSource
    |>.toThetaPilotArithmeticDivisorLocalEvaluationSource

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource
        place estimate) :
    Prop :=
  source.arithmeticDivisorSource.Endpoint ∧
    source.propositionLogShellFormulaSource.Endpoint ∧
      IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource.Endpoint
        source.toFormulaArithmeticDivisorEvaluationSource ∧
        IUTStage1IUTIVTheorem110ArithmeticDivisorEvaluationSource.Endpoint
          source.toTheorem110ArithmeticDivisorEvaluationSource ∧
          IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource.Endpoint
            source.toThetaPilotArithmeticDivisorLocalEvaluationSource

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource
        place estimate) :
    Endpoint source :=
  ⟨source.arithmeticDivisorSource.endpoint,
    source.propositionLogShellFormulaSource.endpoint,
    source.toFormulaArithmeticDivisorEvaluationSource.endpoint,
    source.toTheorem110ArithmeticDivisorEvaluationSource.endpoint,
    source.toThetaPilotArithmeticDivisorLocalEvaluationSource.endpoint⟩

end IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource

set_option linter.style.longLine false in
/--
Per-place local analytic construction source for IUT IV, Theorem 1.10.

This lowers `IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource` by
requiring the Step (v), Step (vi), and Step (vii) local entries to come from
the construction sources for Proposition 1.4(i),(iii),(iv) and
Proposition 1.5(iii),(iv).  The distinguished and archimedean comparison with
the arithmetic-minus-main-log gap remains outside this record, since that is
the Step (xi)/IUT IV matching still to be constructed.
-/
structure IUTStage1IUTIVTheorem110LocalAnalyticConstructionFormulaSource
    (place : Type u) [Fintype place]
    {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
    (divisorSource :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate)
    (α : Type v) (η : Type w) (K : place -> Type x)
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (archIndex archSummand : place -> Type v)
    [∀ placeId : place, Fintype (archIndex placeId)]
    [∀ placeId : place, Fintype (archSummand placeId)] where
  localKind : place -> IUTStage1IUTIVTheorem110LocalEstimateKind
  localPrimeErrorContribution : place -> Real
  localMainLogContribution : place -> Real
  distinguishedProcessionBound : place -> Real
  archimedeanProcessionBound : place -> Real
  localPrimeErrorContribution_nonneg :
    ∀ placeId : place, 0 <= localPrimeErrorContribution placeId
  primeErrorContribution_eq_sum :
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ placeId : place, localPrimeErrorContribution placeId
  mainLogTerm_eq_sum :
    estimate.mainLogTerm =
      ∑ placeId : place, localMainLogContribution placeId
  distinguishedLogShellConstruction :
    ∀ placeId : place,
      localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
        IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource
          α η (K placeId) hullSystem estimate.l
          (distinguishedProcessionBound placeId)
  nondistinguishedLogShellConstruction :
    ∀ placeId : place,
      localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean ->
        IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource
          α η (K placeId) hullSystem
          (divisorSource.localArithmeticUpperContribution
              localPrimeErrorContribution placeId -
            localMainLogContribution placeId)
  archimedeanMetricConstruction :
    ∀ placeId : place,
      localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
        IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
          (archIndex placeId) (archSummand placeId) estimate.l
          (archimedeanProcessionBound placeId)

namespace IUTStage1IUTIVTheorem110LocalAnalyticConstructionFormulaSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {divisorSource :
  IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate}
variable {α : Type v} {η : Type w} {K : place -> Type x}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {archIndex archSummand : place -> Type v}
variable [∀ placeId : place, Fintype (archIndex placeId)]
variable [∀ placeId : place, Fintype (archSummand placeId)]

set_option linter.style.longLine false in
noncomputable def toPropositionLogShellFormulaSource
    (source :
      IUTStage1IUTIVTheorem110LocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource
      place divisorSource :=
  { localKind := source.localKind,
    localPrimeErrorContribution := source.localPrimeErrorContribution,
    localMainLogContribution := source.localMainLogContribution,
    distinguishedProcessionBound :=
      source.distinguishedProcessionBound,
    archimedeanProcessionBound :=
      source.archimedeanProcessionBound,
    localPrimeErrorContribution_nonneg :=
      source.localPrimeErrorContribution_nonneg,
    primeErrorContribution_eq_sum :=
      source.primeErrorContribution_eq_sum,
    mainLogTerm_eq_sum :=
      source.mainLogTerm_eq_sum,
    distinguishedLogShellEstimate := by
      intro placeId hkind
      exact
        (source.distinguishedLogShellConstruction placeId hkind)
          |>.toDistinguishedLocalLogShellEstimate,
    nondistinguishedLogShellEstimate := by
      intro placeId hkind
      exact
        (source.nondistinguishedLogShellConstruction placeId hkind)
          |>.toNondistinguishedLocalLogShellEstimate,
    archimedeanMetricEstimate := by
      intro placeId hkind
      exact
        (source.archimedeanMetricConstruction placeId hkind)
          |>.toArchimedeanLocalMetricEstimate }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110LocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand) :
    Prop :=
  (∀ placeId : place,
      0 <= source.localPrimeErrorContribution placeId) ∧
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ placeId : place, source.localPrimeErrorContribution placeId ∧
    estimate.mainLogTerm =
      ∑ placeId : place, source.localMainLogContribution placeId ∧
    (∀ placeId : place,
      (hkind :
        source.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        (source.distinguishedLogShellConstruction placeId hkind).Endpoint) ∧
    (∀ placeId : place,
      (hkind :
        source.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean) ->
        (source.nondistinguishedLogShellConstruction placeId hkind).Endpoint) ∧
    (∀ placeId : place,
      (hkind :
        source.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        (source.archimedeanMetricConstruction placeId hkind).Endpoint) ∧
    source.toPropositionLogShellFormulaSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110LocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand) :
    Endpoint source :=
  ⟨source.localPrimeErrorContribution_nonneg,
    source.primeErrorContribution_eq_sum,
    source.mainLogTerm_eq_sum,
    (fun placeId hkind =>
      (source.distinguishedLogShellConstruction placeId hkind).endpoint),
    (fun placeId hkind =>
      (source.nondistinguishedLogShellConstruction placeId hkind).endpoint),
    (fun placeId hkind =>
      (source.archimedeanMetricConstruction placeId hkind).endpoint),
    source.toPropositionLogShellFormulaSource.endpoint⟩

end IUTStage1IUTIVTheorem110LocalAnalyticConstructionFormulaSource

set_option linter.style.longLine false in
/--
Arithmetic-divisor evaluation source backed by local analytic constructions of
the Proposition 1.4/1.5 estimates.
-/
structure IUTStage1IUTIVTheorem110LocalAnalyticArithmeticDivisorEvaluationSource
    (place : Type u) [Fintype place]
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (α : Type v) (η : Type w) (K : place -> Type x)
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (archIndex archSummand : place -> Type v)
    [∀ placeId : place, Fintype (archIndex placeId)]
    [∀ placeId : place, Fintype (archSummand placeId)] where
  arithmeticDivisorSource :
    IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate
  localAnalyticConstructionFormulaSource :
    IUTStage1IUTIVTheorem110LocalAnalyticConstructionFormulaSource
      place arithmeticDivisorSource α η K hullSystem archIndex archSummand
  distinguished_formula_le_gap :
    ∀ placeId : place,
      localAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
        localAnalyticConstructionFormulaSource.distinguishedProcessionBound
            placeId <=
          arithmeticDivisorSource.localArithmeticUpperContribution
              localAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            localAnalyticConstructionFormulaSource.localMainLogContribution
              placeId
  archimedean_formula_le_gap :
    ∀ placeId : place,
      localAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
        localAnalyticConstructionFormulaSource.archimedeanProcessionBound
            placeId <=
          arithmeticDivisorSource.localArithmeticUpperContribution
              localAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            localAnalyticConstructionFormulaSource.localMainLogContribution
              placeId

namespace IUTStage1IUTIVTheorem110LocalAnalyticArithmeticDivisorEvaluationSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {α : Type v} {η : Type w} {K : place -> Type x}
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {archIndex archSummand : place -> Type v}
variable [∀ placeId : place, Fintype (archIndex placeId)]
variable [∀ placeId : place, Fintype (archSummand placeId)]

set_option linter.style.longLine false in
noncomputable def toPropositionArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110LocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource
      place estimate :=
  { arithmeticDivisorSource := source.arithmeticDivisorSource,
    propositionLogShellFormulaSource :=
      source.localAnalyticConstructionFormulaSource
        |>.toPropositionLogShellFormulaSource,
    distinguished_formula_le_gap :=
      source.distinguished_formula_le_gap,
    archimedean_formula_le_gap :=
      source.archimedean_formula_le_gap }

noncomputable def toFormulaArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110LocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource
      place estimate :=
  source.toPropositionArithmeticDivisorEvaluationSource
    |>.toFormulaArithmeticDivisorEvaluationSource

noncomputable def toThetaPilotArithmeticDivisorLocalEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110LocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
      place estimate :=
  source.toPropositionArithmeticDivisorEvaluationSource
    |>.toThetaPilotArithmeticDivisorLocalEvaluationSource

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110LocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    Prop :=
  source.arithmeticDivisorSource.Endpoint ∧
    source.localAnalyticConstructionFormulaSource.Endpoint ∧
      IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource.Endpoint
        source.toPropositionArithmeticDivisorEvaluationSource ∧
        IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource.Endpoint
          source.toFormulaArithmeticDivisorEvaluationSource ∧
          IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource.Endpoint
            source.toThetaPilotArithmeticDivisorLocalEvaluationSource

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110LocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    Endpoint source :=
  ⟨source.arithmeticDivisorSource.endpoint,
    source.localAnalyticConstructionFormulaSource.endpoint,
    source.toPropositionArithmeticDivisorEvaluationSource.endpoint,
    source.toFormulaArithmeticDivisorEvaluationSource.endpoint,
    source.toThetaPilotArithmeticDivisorLocalEvaluationSource.endpoint⟩

end IUTStage1IUTIVTheorem110LocalAnalyticArithmeticDivisorEvaluationSource

set_option linter.style.longLine false in
/--
Distinguished Proposition 1.4 log-shell source backed by valuation-ball
additive Haar normalization.

This is the local nonarchimedean specialization of the additive-Haar source:
the ring of integers and compact open subset are valuation balls, and the
uniformizer dilation/Haar scaling data are supplied by
`IUTStage1ValuationBallAdditiveHaarNormalizationSource`.
-/
structure IUTStage1IUTIVProposition14DistinguishedValuationBallAdditiveHaarLogShellSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K] [T2Space K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive)
    (distinguishedProcessionBound : Real) where
  valuationBallHaarSource :
    IUTStage1ValuationBallAdditiveHaarNormalizationSource
      α η K hullSystem
  lambda : Real
  dI : Real
  exceptionalCard : Nat
  exceptionalRamificationLogSum : Real
  shiftedLogUnitsRegion : Set α
  shiftedTensorRegion : Set α
  shiftedLogUnitsLogVolume : Real
  shiftedTensorLogVolume : Real
  shiftedLogUnits_logVolume_eq :
    shiftedLogUnitsLogVolume =
      hullSystem.logVolume shiftedLogUnitsRegion
  shiftedTensor_logVolume_eq :
    shiftedTensorLogVolume =
      hullSystem.logVolume shiftedTensorRegion
  prop14_logUnits_le_first_bound :
    shiftedLogUnitsLogVolume <=
      iutIVProp14DistinguishedLogUnitsFirstBound
        valuationBallHaarSource.residuePrime lambda dI exceptionalCard
  prop14_tensor_le_second_bound :
    shiftedTensorLogVolume <=
      iutIVProp14DistinguishedTensorBound
        valuationBallHaarSource.residuePrime lambda dI
        exceptionalRamificationLogSum
  prop14_first_bound_le_weighted_average :
    iutIVProp14DistinguishedLogUnitsFirstBound
        valuationBallHaarSource.residuePrime lambda dI exceptionalCard <=
      iutIVProp14DistinguishedTensorBound
        valuationBallHaarSource.residuePrime lambda dI
        exceptionalRamificationLogSum
  exactProcessionNormalizedUpperBound : Real
  coarseProcessionNormalizedUpperBound : Real
  proposition17_weighted_average_le_exact_procession :
    iutIVProp14DistinguishedTensorBound
        valuationBallHaarSource.residuePrime lambda dI
        exceptionalRamificationLogSum <=
      exactProcessionNormalizedUpperBound
  stepV_exact_procession_le_coarse :
    exactProcessionNormalizedUpperBound <=
      coarseProcessionNormalizedUpperBound
  stepV_coarse_le_formula_bound :
    coarseProcessionNormalizedUpperBound <= distinguishedProcessionBound

namespace IUTStage1IUTIVProposition14DistinguishedValuationBallAdditiveHaarLogShellSource

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K] [T2Space K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {l : PrimeGeFive}
variable {distinguishedProcessionBound : Real}

noncomputable def toAdditiveHaarLogShellSource
    (source :
      IUTStage1IUTIVProposition14DistinguishedValuationBallAdditiveHaarLogShellSource
        α η K hullSystem l distinguishedProcessionBound) :
    IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound :=
  { additiveHaarSource :=
      source.valuationBallHaarSource.toAdditiveHaarCompactOpenNormalizationSource,
    lambda := source.lambda,
    dI := source.dI,
    exceptionalCard := source.exceptionalCard,
    exceptionalRamificationLogSum :=
      source.exceptionalRamificationLogSum,
    shiftedLogUnitsRegion := source.shiftedLogUnitsRegion,
    shiftedTensorRegion := source.shiftedTensorRegion,
    shiftedLogUnitsLogVolume := source.shiftedLogUnitsLogVolume,
    shiftedTensorLogVolume := source.shiftedTensorLogVolume,
    shiftedLogUnits_logVolume_eq :=
      source.shiftedLogUnits_logVolume_eq,
    shiftedTensor_logVolume_eq :=
      source.shiftedTensor_logVolume_eq,
    prop14_logUnits_le_first_bound :=
      source.prop14_logUnits_le_first_bound,
    prop14_tensor_le_second_bound :=
      source.prop14_tensor_le_second_bound,
    prop14_first_bound_le_weighted_average :=
      source.prop14_first_bound_le_weighted_average,
    exactProcessionNormalizedUpperBound :=
      source.exactProcessionNormalizedUpperBound,
    coarseProcessionNormalizedUpperBound :=
      source.coarseProcessionNormalizedUpperBound,
    proposition17_weighted_average_le_exact_procession :=
      source.proposition17_weighted_average_le_exact_procession,
    stepV_exact_procession_le_coarse :=
      source.stepV_exact_procession_le_coarse,
    stepV_coarse_le_formula_bound :=
      source.stepV_coarse_le_formula_bound }

noncomputable def toCompactOpenHaarLogShellSource
    (source :
      IUTStage1IUTIVProposition14DistinguishedValuationBallAdditiveHaarLogShellSource
        α η K hullSystem l distinguishedProcessionBound) :
    IUTStage1IUTIVProposition14DistinguishedCompactOpenHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound :=
  source.toAdditiveHaarLogShellSource.toCompactOpenHaarLogShellSource

noncomputable def toDistinguishedLocalLogShellConstructionSource
    (source :
      IUTStage1IUTIVProposition14DistinguishedValuationBallAdditiveHaarLogShellSource
        α η K hullSystem l distinguishedProcessionBound) :
    IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource
      α η K hullSystem l distinguishedProcessionBound :=
  source.toAdditiveHaarLogShellSource
    |>.toDistinguishedLocalLogShellConstructionSource

def Endpoint
    (source :
      IUTStage1IUTIVProposition14DistinguishedValuationBallAdditiveHaarLogShellSource
        α η K hullSystem l distinguishedProcessionBound) :
    Prop :=
  IUTStage1ValuationBallAdditiveHaarNormalizationSource.ValuationBallAdditiveHaarNormalizationAudit
      source.valuationBallHaarSource ∧
    source.toAdditiveHaarLogShellSource.Endpoint ∧
      source.toCompactOpenHaarLogShellSource.Endpoint ∧
        source.toDistinguishedLocalLogShellConstructionSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVProposition14DistinguishedValuationBallAdditiveHaarLogShellSource
        α η K hullSystem l distinguishedProcessionBound) :
    Endpoint source :=
  ⟨IUTStage1ValuationBallAdditiveHaarNormalizationSource.valuationBallAdditiveHaarNormalizationAudit
      source.valuationBallHaarSource,
    source.toAdditiveHaarLogShellSource.endpoint,
    source.toCompactOpenHaarLogShellSource.endpoint,
    source.toDistinguishedLocalLogShellConstructionSource.endpoint⟩

end IUTStage1IUTIVProposition14DistinguishedValuationBallAdditiveHaarLogShellSource

set_option linter.style.longLine false in
/--
Nondistinguished Proposition 1.4 log-shell source backed by valuation-ball
additive Haar normalization.

The tensor container is identified with the normalized integral valuation ball,
so Proposition 1.4(iv)'s zero log-volume statement is inherited from the
valuation-ball Haar normalization audit.
-/
structure IUTStage1IUTIVProposition14NondistinguishedValuationBallAdditiveHaarLogShellSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K] [T2Space K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (localArithmeticMinusMainGap : Real) where
  valuationBallHaarSource :
    IUTStage1ValuationBallAdditiveHaarNormalizationSource
      α η K hullSystem
  tensorContainerRegion : Set α
  tensorContainerLogVolume : Real
  tensorContainerRegion_eq_integralRegion :
    tensorContainerRegion =
      valuationBallHaarSource.realizedRegion valuationBallHaarSource.ringOfIntegers
  tensorContainerLogVolume_eq_hull :
    tensorContainerLogVolume =
      hullSystem.logVolume tensorContainerRegion
  prop14_phi_preserves_tensorContainer : Prop
  prop14_phi_preserves_tensorContainer_holds :
    prop14_phi_preserves_tensorContainer
  prop14_zero_le_gap :
    0 <= localArithmeticMinusMainGap

namespace IUTStage1IUTIVProposition14NondistinguishedValuationBallAdditiveHaarLogShellSource

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K] [T2Space K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {localArithmeticMinusMainGap : Real}

noncomputable def toAdditiveHaarLogShellSource
    (source :
      IUTStage1IUTIVProposition14NondistinguishedValuationBallAdditiveHaarLogShellSource
        α η K hullSystem localArithmeticMinusMainGap) :
    IUTStage1IUTIVProposition14NondistinguishedAdditiveHaarLogShellSource
      α η K hullSystem localArithmeticMinusMainGap :=
  { additiveHaarSource :=
      source.valuationBallHaarSource.toAdditiveHaarCompactOpenNormalizationSource,
    tensorContainerRegion := source.tensorContainerRegion,
    tensorContainerLogVolume := source.tensorContainerLogVolume,
    tensorContainerRegion_eq_integralRegion :=
      source.tensorContainerRegion_eq_integralRegion,
    tensorContainerLogVolume_eq_hull :=
      source.tensorContainerLogVolume_eq_hull,
    prop14_phi_preserves_tensorContainer :=
      source.prop14_phi_preserves_tensorContainer,
    prop14_phi_preserves_tensorContainer_holds :=
      source.prop14_phi_preserves_tensorContainer_holds,
    prop14_zero_le_gap :=
      source.prop14_zero_le_gap }

noncomputable def toCompactOpenHaarLogShellSource
    (source :
      IUTStage1IUTIVProposition14NondistinguishedValuationBallAdditiveHaarLogShellSource
        α η K hullSystem localArithmeticMinusMainGap) :
    IUTStage1IUTIVProposition14NondistinguishedCompactOpenHaarLogShellSource
      α η K hullSystem localArithmeticMinusMainGap :=
  source.toAdditiveHaarLogShellSource.toCompactOpenHaarLogShellSource

noncomputable def toNondistinguishedLocalLogShellConstructionSource
    (source :
      IUTStage1IUTIVProposition14NondistinguishedValuationBallAdditiveHaarLogShellSource
        α η K hullSystem localArithmeticMinusMainGap) :
    IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource
      α η K hullSystem localArithmeticMinusMainGap :=
  source.toAdditiveHaarLogShellSource
    |>.toNondistinguishedLocalLogShellConstructionSource

def Endpoint
    (source :
      IUTStage1IUTIVProposition14NondistinguishedValuationBallAdditiveHaarLogShellSource
        α η K hullSystem localArithmeticMinusMainGap) :
    Prop :=
  IUTStage1ValuationBallAdditiveHaarNormalizationSource.ValuationBallAdditiveHaarNormalizationAudit
      source.valuationBallHaarSource ∧
    source.toAdditiveHaarLogShellSource.Endpoint ∧
      source.toCompactOpenHaarLogShellSource.Endpoint ∧
        source.toNondistinguishedLocalLogShellConstructionSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVProposition14NondistinguishedValuationBallAdditiveHaarLogShellSource
        α η K hullSystem localArithmeticMinusMainGap) :
    Endpoint source :=
  ⟨IUTStage1ValuationBallAdditiveHaarNormalizationSource.valuationBallAdditiveHaarNormalizationAudit
      source.valuationBallHaarSource,
    source.toAdditiveHaarLogShellSource.endpoint,
    source.toCompactOpenHaarLogShellSource.endpoint,
    source.toNondistinguishedLocalLogShellConstructionSource.endpoint⟩

end IUTStage1IUTIVProposition14NondistinguishedValuationBallAdditiveHaarLogShellSource

set_option linter.style.longLine false in
/--
Valuation-ball additive-Haar local analytic construction source for IUT IV,
Theorem 1.10.

Finite nonarchimedean places now provide Proposition 1.4 data through actual
valuation balls and additive Haar normalization before projecting to the
additive-Haar local analytic construction used by the current corridor.
-/
structure IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
    (place : Type u) [Fintype place]
    {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
    (divisorSource :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate)
    (α : Type v) (η : Type w) (K : place -> Type x)
    [∀ placeId : place, TopologicalSpace (K placeId)]
    [∀ placeId : place, MeasurableSpace (K placeId)]
    [∀ placeId : place, AddGroup (K placeId)]
    [∀ placeId : place, T2Space (K placeId)]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (archIndex archSummand : place -> Type v)
    [∀ placeId : place, Fintype (archIndex placeId)]
    [∀ placeId : place, Fintype (archSummand placeId)] where
  localKind : place -> IUTStage1IUTIVTheorem110LocalEstimateKind
  localPrimeErrorContribution : place -> Real
  localMainLogContribution : place -> Real
  distinguishedProcessionBound : place -> Real
  archimedeanProcessionBound : place -> Real
  localPrimeErrorContribution_nonneg :
    ∀ placeId : place, 0 <= localPrimeErrorContribution placeId
  primeErrorContribution_eq_sum :
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ placeId : place, localPrimeErrorContribution placeId
  mainLogTerm_eq_sum :
    estimate.mainLogTerm =
      ∑ placeId : place, localMainLogContribution placeId
  distinguishedValuationBallAdditiveHaarLogShellConstruction :
    ∀ placeId : place,
      localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
        IUTStage1IUTIVProposition14DistinguishedValuationBallAdditiveHaarLogShellSource
          α η (K placeId) hullSystem estimate.l
          (distinguishedProcessionBound placeId)
  nondistinguishedValuationBallAdditiveHaarLogShellConstruction :
    ∀ placeId : place,
      localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean ->
        IUTStage1IUTIVProposition14NondistinguishedValuationBallAdditiveHaarLogShellSource
          α η (K placeId) hullSystem
          (divisorSource.localArithmeticUpperContribution
              localPrimeErrorContribution placeId -
            localMainLogContribution placeId)
  archimedeanMetricConstruction :
    ∀ placeId : place,
      localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
        IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
          (archIndex placeId) (archSummand placeId) estimate.l
          (archimedeanProcessionBound placeId)

set_option linter.style.longLine false in
/--
Additive Haar backed local analytic construction source for IUT IV,
Theorem 1.10.

This refines `IUTStage1IUTIVTheorem110LocalAnalyticConstructionFormulaSource`
at the nonarchimedean places: the Proposition 1.4 entries now consume
compact-open additive Haar normalization data, then project through the
compact-open and finite-extension Haar layers already used by the established
local analytic route.
-/
structure IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticConstructionFormulaSource
    (place : Type u) [Fintype place]
    {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
    (divisorSource :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate)
    (α : Type v) (η : Type w) (K : place -> Type x)
    [∀ placeId : place, TopologicalSpace (K placeId)]
    [∀ placeId : place, MeasurableSpace (K placeId)]
    [∀ placeId : place, AddGroup (K placeId)]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (archIndex archSummand : place -> Type v)
    [∀ placeId : place, Fintype (archIndex placeId)]
    [∀ placeId : place, Fintype (archSummand placeId)] where
  localKind : place -> IUTStage1IUTIVTheorem110LocalEstimateKind
  localPrimeErrorContribution : place -> Real
  localMainLogContribution : place -> Real
  distinguishedProcessionBound : place -> Real
  archimedeanProcessionBound : place -> Real
  localPrimeErrorContribution_nonneg :
    ∀ placeId : place, 0 <= localPrimeErrorContribution placeId
  primeErrorContribution_eq_sum :
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ placeId : place, localPrimeErrorContribution placeId
  mainLogTerm_eq_sum :
    estimate.mainLogTerm =
      ∑ placeId : place, localMainLogContribution placeId
  distinguishedAdditiveHaarLogShellConstruction :
    ∀ placeId : place,
      localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
        IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
          α η (K placeId) hullSystem estimate.l
          (distinguishedProcessionBound placeId)
  nondistinguishedAdditiveHaarLogShellConstruction :
    ∀ placeId : place,
      localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean ->
        IUTStage1IUTIVProposition14NondistinguishedAdditiveHaarLogShellSource
          α η (K placeId) hullSystem
          (divisorSource.localArithmeticUpperContribution
              localPrimeErrorContribution placeId -
            localMainLogContribution placeId)
  archimedeanMetricConstruction :
    ∀ placeId : place,
      localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
        IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
          (archIndex placeId) (archSummand placeId) estimate.l
          (archimedeanProcessionBound placeId)

namespace IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticConstructionFormulaSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {divisorSource :
  IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate}
variable {α : Type v} {η : Type w} {K : place -> Type x}
variable [∀ placeId : place, TopologicalSpace (K placeId)]
variable [∀ placeId : place, MeasurableSpace (K placeId)]
variable [∀ placeId : place, AddGroup (K placeId)]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {archIndex archSummand : place -> Type v}
variable [∀ placeId : place, Fintype (archIndex placeId)]
variable [∀ placeId : place, Fintype (archSummand placeId)]

set_option linter.style.longLine false in
noncomputable def toLocalAnalyticConstructionFormulaSource
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110LocalAnalyticConstructionFormulaSource
      place divisorSource α η K hullSystem archIndex archSummand :=
  { localKind := source.localKind,
    localPrimeErrorContribution := source.localPrimeErrorContribution,
    localMainLogContribution := source.localMainLogContribution,
    distinguishedProcessionBound :=
      source.distinguishedProcessionBound,
    archimedeanProcessionBound :=
      source.archimedeanProcessionBound,
    localPrimeErrorContribution_nonneg :=
      source.localPrimeErrorContribution_nonneg,
    primeErrorContribution_eq_sum :=
      source.primeErrorContribution_eq_sum,
    mainLogTerm_eq_sum :=
      source.mainLogTerm_eq_sum,
    distinguishedLogShellConstruction := by
      intro placeId hkind
      exact
        (source.distinguishedAdditiveHaarLogShellConstruction placeId hkind)
          |>.toDistinguishedLocalLogShellConstructionSource,
    nondistinguishedLogShellConstruction := by
      intro placeId hkind
      exact
        (source.nondistinguishedAdditiveHaarLogShellConstruction placeId hkind)
          |>.toNondistinguishedLocalLogShellConstructionSource,
    archimedeanMetricConstruction := source.archimedeanMetricConstruction }

noncomputable def toPropositionLogShellFormulaSource
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource
      place divisorSource :=
  source.toLocalAnalyticConstructionFormulaSource
    |>.toPropositionLogShellFormulaSource

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand) :
    Prop :=
  (∀ placeId : place,
      0 <= source.localPrimeErrorContribution placeId) ∧
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ placeId : place, source.localPrimeErrorContribution placeId ∧
    estimate.mainLogTerm =
      ∑ placeId : place, source.localMainLogContribution placeId ∧
    (∀ placeId : place,
      (hkind :
        source.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        (source.distinguishedAdditiveHaarLogShellConstruction
          placeId hkind).Endpoint) ∧
    (∀ placeId : place,
      (hkind :
        source.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean) ->
        (source.nondistinguishedAdditiveHaarLogShellConstruction
          placeId hkind).Endpoint) ∧
    (∀ placeId : place,
      (hkind :
        source.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        (source.archimedeanMetricConstruction placeId hkind).Endpoint) ∧
    source.toLocalAnalyticConstructionFormulaSource.Endpoint ∧
    source.toPropositionLogShellFormulaSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand) :
    Endpoint source :=
  ⟨source.localPrimeErrorContribution_nonneg,
    source.primeErrorContribution_eq_sum,
    source.mainLogTerm_eq_sum,
    (fun placeId hkind =>
      (source.distinguishedAdditiveHaarLogShellConstruction placeId hkind).endpoint),
    (fun placeId hkind =>
      (source.nondistinguishedAdditiveHaarLogShellConstruction placeId hkind).endpoint),
    (fun placeId hkind =>
      (source.archimedeanMetricConstruction placeId hkind).endpoint),
    source.toLocalAnalyticConstructionFormulaSource.endpoint,
    source.toPropositionLogShellFormulaSource.endpoint⟩

end IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticConstructionFormulaSource

namespace IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {divisorSource :
  IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate}
variable {α : Type v} {η : Type w} {K : place -> Type x}
variable [∀ placeId : place, TopologicalSpace (K placeId)]
variable [∀ placeId : place, MeasurableSpace (K placeId)]
variable [∀ placeId : place, AddGroup (K placeId)]
variable [∀ placeId : place, T2Space (K placeId)]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {archIndex archSummand : place -> Type v}
variable [∀ placeId : place, Fintype (archIndex placeId)]
variable [∀ placeId : place, Fintype (archSummand placeId)]

set_option linter.style.longLine false in
noncomputable def toAdditiveHaarLocalAnalyticConstructionFormulaSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticConstructionFormulaSource
      place divisorSource α η K hullSystem archIndex archSummand :=
  { localKind := source.localKind,
    localPrimeErrorContribution := source.localPrimeErrorContribution,
    localMainLogContribution := source.localMainLogContribution,
    distinguishedProcessionBound :=
      source.distinguishedProcessionBound,
    archimedeanProcessionBound :=
      source.archimedeanProcessionBound,
    localPrimeErrorContribution_nonneg :=
      source.localPrimeErrorContribution_nonneg,
    primeErrorContribution_eq_sum :=
      source.primeErrorContribution_eq_sum,
    mainLogTerm_eq_sum :=
      source.mainLogTerm_eq_sum,
    distinguishedAdditiveHaarLogShellConstruction := by
      intro placeId hkind
      exact
        (source.distinguishedValuationBallAdditiveHaarLogShellConstruction
          placeId hkind).toAdditiveHaarLogShellSource,
    nondistinguishedAdditiveHaarLogShellConstruction := by
      intro placeId hkind
      exact
        (source.nondistinguishedValuationBallAdditiveHaarLogShellConstruction
          placeId hkind).toAdditiveHaarLogShellSource,
    archimedeanMetricConstruction :=
      source.archimedeanMetricConstruction }

noncomputable def toLocalAnalyticConstructionFormulaSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110LocalAnalyticConstructionFormulaSource
      place divisorSource α η K hullSystem archIndex archSummand :=
  source.toAdditiveHaarLocalAnalyticConstructionFormulaSource
    |>.toLocalAnalyticConstructionFormulaSource

noncomputable def toPropositionLogShellFormulaSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource
      place divisorSource :=
  source.toAdditiveHaarLocalAnalyticConstructionFormulaSource
    |>.toPropositionLogShellFormulaSource

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand) :
    Prop :=
  (∀ placeId : place,
      0 <= source.localPrimeErrorContribution placeId) ∧
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ placeId : place, source.localPrimeErrorContribution placeId ∧
    estimate.mainLogTerm =
      ∑ placeId : place, source.localMainLogContribution placeId ∧
    (∀ placeId : place,
      (hkind :
        source.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        (source.distinguishedValuationBallAdditiveHaarLogShellConstruction
          placeId hkind).Endpoint) ∧
    (∀ placeId : place,
      (hkind :
        source.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean) ->
        (source.nondistinguishedValuationBallAdditiveHaarLogShellConstruction
          placeId hkind).Endpoint) ∧
    (∀ placeId : place,
      (hkind :
        source.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        (source.archimedeanMetricConstruction placeId hkind).Endpoint) ∧
    source.toAdditiveHaarLocalAnalyticConstructionFormulaSource.Endpoint ∧
    source.toLocalAnalyticConstructionFormulaSource.Endpoint ∧
    source.toPropositionLogShellFormulaSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand) :
    Endpoint source :=
  ⟨source.localPrimeErrorContribution_nonneg,
    source.primeErrorContribution_eq_sum,
    source.mainLogTerm_eq_sum,
    (fun placeId hkind =>
      (source.distinguishedValuationBallAdditiveHaarLogShellConstruction
        placeId hkind).endpoint),
    (fun placeId hkind =>
      (source.nondistinguishedValuationBallAdditiveHaarLogShellConstruction
        placeId hkind).endpoint),
    (fun placeId hkind =>
      (source.archimedeanMetricConstruction placeId hkind).endpoint),
    source.toAdditiveHaarLocalAnalyticConstructionFormulaSource.endpoint,
    source.toLocalAnalyticConstructionFormulaSource.endpoint,
    source.toPropositionLogShellFormulaSource.endpoint⟩

set_option linter.style.longLine false in
theorem nondistinguished_zero_le_gap
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand)
    (placeId : place)
    (hkind :
      source.localKind placeId =
        IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean) :
    0 <=
      divisorSource.localArithmeticUpperContribution
        source.localPrimeErrorContribution placeId -
          source.localMainLogContribution placeId :=
  (source.nondistinguishedValuationBallAdditiveHaarLogShellConstruction
    placeId hkind).prop14_zero_le_gap

end IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource

set_option linter.style.longLine false in
/--
Valuation-ball local analytic construction with a selected distinguished
nonarchimedean place.

This refines the valuation-ball Theorem 1.10 local source by making the
distinguished p-adic place part of the source's case definition.  The local
kind is definitionally distinguished at `selectedDistinguishedPlace`; away
from that place it is read from `residualLocalKind`.  This is the source-level
place-selection layer needed by the p-adic Haar route: downstream proofs of
`localKind selected = distinguishedNonarchimedean` are no longer separate
public inputs.
-/
structure IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
    (place : Type u) [Fintype place]
    {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
    (divisorSource :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate)
    (α : Type v) (η : Type w) (K : place -> Type x)
    [∀ placeId : place, TopologicalSpace (K placeId)]
    [∀ placeId : place, MeasurableSpace (K placeId)]
    [∀ placeId : place, AddGroup (K placeId)]
    [∀ placeId : place, T2Space (K placeId)]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (archIndex archSummand : place -> Type v)
    [∀ placeId : place, Fintype (archIndex placeId)]
    [∀ placeId : place, Fintype (archSummand placeId)]
    (selectedDistinguishedPlace : place) where
  residualLocalKind : place -> IUTStage1IUTIVTheorem110LocalEstimateKind
  localPrimeErrorContribution : place -> Real
  localMainLogContribution : place -> Real
  distinguishedProcessionBound : place -> Real
  archimedeanProcessionBound : place -> Real
  localPrimeErrorContribution_nonneg :
    ∀ placeId : place, 0 <= localPrimeErrorContribution placeId
  primeErrorContribution_eq_sum :
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ placeId : place, localPrimeErrorContribution placeId
  mainLogTerm_eq_sum :
    estimate.mainLogTerm =
      ∑ placeId : place, localMainLogContribution placeId
  selectedDistinguishedValuationBallAdditiveHaarLogShellConstruction :
    IUTStage1IUTIVProposition14DistinguishedValuationBallAdditiveHaarLogShellSource
      α η (K selectedDistinguishedPlace) hullSystem estimate.l
      (distinguishedProcessionBound selectedDistinguishedPlace)
  residualDistinguishedValuationBallAdditiveHaarLogShellConstruction :
    ∀ placeId : place,
      placeId ≠ selectedDistinguishedPlace ->
        residualLocalKind placeId =
            IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
          IUTStage1IUTIVProposition14DistinguishedValuationBallAdditiveHaarLogShellSource
            α η (K placeId) hullSystem estimate.l
            (distinguishedProcessionBound placeId)
  residualNondistinguishedValuationBallAdditiveHaarLogShellConstruction :
    ∀ placeId : place,
      placeId ≠ selectedDistinguishedPlace ->
        residualLocalKind placeId =
            IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean ->
          IUTStage1IUTIVProposition14NondistinguishedValuationBallAdditiveHaarLogShellSource
            α η (K placeId) hullSystem
            (divisorSource.localArithmeticUpperContribution
                localPrimeErrorContribution placeId -
              localMainLogContribution placeId)
  residualArchimedeanMetricConstruction :
    ∀ placeId : place,
      placeId ≠ selectedDistinguishedPlace ->
        residualLocalKind placeId =
            IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
          IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
            (archIndex placeId) (archSummand placeId) estimate.l
            (archimedeanProcessionBound placeId)

namespace IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {divisorSource :
  IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate}
variable {α : Type v} {η : Type w} {K : place -> Type x}
variable [∀ placeId : place, TopologicalSpace (K placeId)]
variable [∀ placeId : place, MeasurableSpace (K placeId)]
variable [∀ placeId : place, AddGroup (K placeId)]
variable [∀ placeId : place, T2Space (K placeId)]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {archIndex archSummand : place -> Type v}
variable [∀ placeId : place, Fintype (archIndex placeId)]
variable [∀ placeId : place, Fintype (archSummand placeId)]
variable {selectedDistinguishedPlace : place}

noncomputable def localKind
    (source :
      IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand
        selectedDistinguishedPlace)
    (placeId : place) :
    IUTStage1IUTIVTheorem110LocalEstimateKind := by
  classical
  exact
    if placeId = selectedDistinguishedPlace then
      IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean
    else
      source.residualLocalKind placeId

@[simp] theorem localKind_selectedDistinguishedPlace
    (source :
      IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand
        selectedDistinguishedPlace) :
    source.localKind selectedDistinguishedPlace =
      IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean := by
  classical
  simp [localKind]

set_option linter.style.longLine false in
noncomputable def toValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
    (source :
      IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand
        selectedDistinguishedPlace) :
    IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
      place divisorSource α η K hullSystem archIndex archSummand :=
  { localKind := source.localKind,
    localPrimeErrorContribution := source.localPrimeErrorContribution,
    localMainLogContribution := source.localMainLogContribution,
    distinguishedProcessionBound := source.distinguishedProcessionBound,
    archimedeanProcessionBound := source.archimedeanProcessionBound,
    localPrimeErrorContribution_nonneg :=
      source.localPrimeErrorContribution_nonneg,
    primeErrorContribution_eq_sum :=
      source.primeErrorContribution_eq_sum,
    mainLogTerm_eq_sum :=
      source.mainLogTerm_eq_sum,
    distinguishedValuationBallAdditiveHaarLogShellConstruction := by
      classical
      intro placeId hkind
      by_cases hplace : placeId = selectedDistinguishedPlace
      · subst hplace
        exact source.selectedDistinguishedValuationBallAdditiveHaarLogShellConstruction
      · exact source.residualDistinguishedValuationBallAdditiveHaarLogShellConstruction
          placeId hplace (by
            simpa [localKind, hplace] using hkind),
    nondistinguishedValuationBallAdditiveHaarLogShellConstruction := by
      classical
      intro placeId hkind
      by_cases hplace : placeId = selectedDistinguishedPlace
      · subst hplace
        exact False.elim (by
          simpa [localKind] using hkind)
      · exact source.residualNondistinguishedValuationBallAdditiveHaarLogShellConstruction
          placeId hplace (by
            simpa [localKind, hplace] using hkind),
    archimedeanMetricConstruction := by
      classical
      intro placeId hkind
      by_cases hplace : placeId = selectedDistinguishedPlace
      · subst hplace
        exact False.elim (by
          simpa [localKind] using hkind)
      · exact source.residualArchimedeanMetricConstruction
          placeId hplace (by
            simpa [localKind, hplace] using hkind) }

set_option linter.style.longLine false in
theorem selectedDistinguishedPlace_kind
    (source :
      IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand
        selectedDistinguishedPlace) :
    source.toValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
        selectedDistinguishedPlace =
      IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean := by
  classical
  simp [
    toValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource,
    localKind]

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand
        selectedDistinguishedPlace) :
    Prop :=
  (∀ placeId : place,
      0 <= source.localPrimeErrorContribution placeId) ∧
    10 * (estimate.eStarMod * (estimate.l.value : Real) + estimate.etaPrm) =
      ∑ placeId : place, source.localPrimeErrorContribution placeId ∧
    estimate.mainLogTerm =
      ∑ placeId : place, source.localMainLogContribution placeId ∧
    source.selectedDistinguishedValuationBallAdditiveHaarLogShellConstruction.Endpoint ∧
    (∀ placeId : place,
      (hneq : placeId ≠ selectedDistinguishedPlace) ->
        (hkind :
          source.residualLocalKind placeId =
            IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
          (source.residualDistinguishedValuationBallAdditiveHaarLogShellConstruction
            placeId hneq hkind).Endpoint) ∧
    (∀ placeId : place,
      (hneq : placeId ≠ selectedDistinguishedPlace) ->
        (hkind :
          source.residualLocalKind placeId =
            IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean) ->
          (source.residualNondistinguishedValuationBallAdditiveHaarLogShellConstruction
            placeId hneq hkind).Endpoint) ∧
    (∀ placeId : place,
      (hneq : placeId ≠ selectedDistinguishedPlace) ->
        (hkind :
          source.residualLocalKind placeId =
            IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
          (source.residualArchimedeanMetricConstruction
            placeId hneq hkind).Endpoint) ∧
    source.toValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.Endpoint

set_option linter.style.longLine false in
theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        place divisorSource α η K hullSystem archIndex archSummand
        selectedDistinguishedPlace) :
    Endpoint source :=
  ⟨source.localPrimeErrorContribution_nonneg,
    source.primeErrorContribution_eq_sum,
    source.mainLogTerm_eq_sum,
    source.selectedDistinguishedValuationBallAdditiveHaarLogShellConstruction.endpoint,
    (fun placeId hneq hkind =>
      (source.residualDistinguishedValuationBallAdditiveHaarLogShellConstruction
        placeId hneq hkind).endpoint),
    (fun placeId hneq hkind =>
      (source.residualNondistinguishedValuationBallAdditiveHaarLogShellConstruction
        placeId hneq hkind).endpoint),
    (fun placeId hneq hkind =>
      (source.residualArchimedeanMetricConstruction
        placeId hneq hkind).endpoint),
    source.toValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.endpoint⟩

end IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource

set_option linter.style.longLine false in
/--
Arithmetic-divisor evaluation source whose Theorem 1.10 local analytic
construction is backed at finite places by additive Haar normalization.
-/
structure IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    (place : Type u) [Fintype place]
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (α : Type v) (η : Type w) (K : place -> Type x)
    [∀ placeId : place, TopologicalSpace (K placeId)]
    [∀ placeId : place, MeasurableSpace (K placeId)]
    [∀ placeId : place, AddGroup (K placeId)]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (archIndex archSummand : place -> Type v)
    [∀ placeId : place, Fintype (archIndex placeId)]
    [∀ placeId : place, Fintype (archSummand placeId)] where
  arithmeticDivisorSource :
    IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate
  additiveHaarLocalAnalyticConstructionFormulaSource :
    IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticConstructionFormulaSource
      place arithmeticDivisorSource α η K hullSystem archIndex archSummand
  distinguished_formula_le_gap :
    ∀ placeId : place,
      additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
        additiveHaarLocalAnalyticConstructionFormulaSource.distinguishedProcessionBound
            placeId <=
          arithmeticDivisorSource.localArithmeticUpperContribution
              additiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            additiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId
  archimedean_formula_le_gap :
    ∀ placeId : place,
      additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
        additiveHaarLocalAnalyticConstructionFormulaSource.archimedeanProcessionBound
            placeId <=
          arithmeticDivisorSource.localArithmeticUpperContribution
              additiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            additiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId

namespace IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {α : Type v} {η : Type w} {K : place -> Type x}
variable [∀ placeId : place, TopologicalSpace (K placeId)]
variable [∀ placeId : place, MeasurableSpace (K placeId)]
variable [∀ placeId : place, AddGroup (K placeId)]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {archIndex archSummand : place -> Type v}
variable [∀ placeId : place, Fintype (archIndex placeId)]
variable [∀ placeId : place, Fintype (archSummand placeId)]

set_option linter.style.longLine false in
noncomputable def toLocalAnalyticArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110LocalAnalyticArithmeticDivisorEvaluationSource
      place estimate α η K hullSystem archIndex archSummand :=
  { arithmeticDivisorSource := source.arithmeticDivisorSource,
    localAnalyticConstructionFormulaSource :=
      source.additiveHaarLocalAnalyticConstructionFormulaSource
        |>.toLocalAnalyticConstructionFormulaSource,
    distinguished_formula_le_gap :=
      source.distinguished_formula_le_gap,
    archimedean_formula_le_gap :=
      source.archimedean_formula_le_gap }

noncomputable def toPropositionArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource
      place estimate :=
  source.toLocalAnalyticArithmeticDivisorEvaluationSource
    |>.toPropositionArithmeticDivisorEvaluationSource

noncomputable def toFormulaArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource
      place estimate :=
  source.toLocalAnalyticArithmeticDivisorEvaluationSource
    |>.toFormulaArithmeticDivisorEvaluationSource

noncomputable def toThetaPilotArithmeticDivisorLocalEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
      place estimate :=
  source.toLocalAnalyticArithmeticDivisorEvaluationSource
    |>.toThetaPilotArithmeticDivisorLocalEvaluationSource

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    Prop :=
  source.arithmeticDivisorSource.Endpoint ∧
    source.additiveHaarLocalAnalyticConstructionFormulaSource.Endpoint ∧
      IUTStage1IUTIVTheorem110LocalAnalyticArithmeticDivisorEvaluationSource.Endpoint
        source.toLocalAnalyticArithmeticDivisorEvaluationSource ∧
        IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource.Endpoint
          source.toPropositionArithmeticDivisorEvaluationSource ∧
          IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource.Endpoint
            source.toFormulaArithmeticDivisorEvaluationSource ∧
            IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource.Endpoint
              source.toThetaPilotArithmeticDivisorLocalEvaluationSource

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    Endpoint source :=
  ⟨source.arithmeticDivisorSource.endpoint,
    source.additiveHaarLocalAnalyticConstructionFormulaSource.endpoint,
    source.toLocalAnalyticArithmeticDivisorEvaluationSource.endpoint,
    source.toPropositionArithmeticDivisorEvaluationSource.endpoint,
    source.toFormulaArithmeticDivisorEvaluationSource.endpoint,
    source.toThetaPilotArithmeticDivisorLocalEvaluationSource.endpoint⟩

end IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource

set_option linter.style.longLine false in
/--
Arithmetic-divisor evaluation source whose Theorem 1.10 local analytic
construction is backed at finite places by valuation-ball additive Haar
normalization.

This is the valuation-ball counterpart of the additive-Haar evaluation source:
finite Proposition 1.4 inputs come from valuation balls and their Haar
normalization audit, then project to the current additive-Haar/local-analytic
Theorem 1.10 route.
-/
structure IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    (place : Type u) [Fintype place]
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (α : Type v) (η : Type w) (K : place -> Type x)
    [∀ placeId : place, TopologicalSpace (K placeId)]
    [∀ placeId : place, MeasurableSpace (K placeId)]
    [∀ placeId : place, AddGroup (K placeId)]
    [∀ placeId : place, T2Space (K placeId)]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (archIndex archSummand : place -> Type v)
    [∀ placeId : place, Fintype (archIndex placeId)]
    [∀ placeId : place, Fintype (archSummand placeId)] where
  arithmeticDivisorSource :
    IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate
  valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource :
    IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
      place arithmeticDivisorSource α η K hullSystem archIndex archSummand
  distinguished_formula_le_gap :
    ∀ placeId : place,
      valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
          placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
        valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.distinguishedProcessionBound
            placeId <=
          arithmeticDivisorSource.localArithmeticUpperContribution
              valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId
  archimedean_formula_le_gap :
    ∀ placeId : place,
      valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
          placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
        valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.archimedeanProcessionBound
            placeId <=
          arithmeticDivisorSource.localArithmeticUpperContribution
              valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId

set_option linter.style.longLine false
namespace IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {α : Type v} {η : Type w} {K : place -> Type x}
variable [∀ placeId : place, TopologicalSpace (K placeId)]
variable [∀ placeId : place, MeasurableSpace (K placeId)]
variable [∀ placeId : place, AddGroup (K placeId)]
variable [∀ placeId : place, T2Space (K placeId)]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {archIndex archSummand : place -> Type v}
variable [∀ placeId : place, Fintype (archIndex placeId)]
variable [∀ placeId : place, Fintype (archSummand placeId)]

set_option linter.style.longLine false in
noncomputable def toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
      place estimate α η K hullSystem archIndex archSummand :=
  { arithmeticDivisorSource := source.arithmeticDivisorSource,
    additiveHaarLocalAnalyticConstructionFormulaSource :=
      source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        |>.toAdditiveHaarLocalAnalyticConstructionFormulaSource,
    distinguished_formula_le_gap :=
      source.distinguished_formula_le_gap,
    archimedean_formula_le_gap :=
      source.archimedean_formula_le_gap }

set_option linter.style.longLine false in
noncomputable def toLocalAnalyticArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110LocalAnalyticArithmeticDivisorEvaluationSource
      place estimate α η K hullSystem archIndex archSummand :=
  source.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    |>.toLocalAnalyticArithmeticDivisorEvaluationSource

set_option linter.style.longLine false in
noncomputable def toPropositionArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource
      place estimate :=
  source.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    |>.toPropositionArithmeticDivisorEvaluationSource

set_option linter.style.longLine false in
noncomputable def toFormulaArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource
      place estimate :=
  source.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    |>.toFormulaArithmeticDivisorEvaluationSource

set_option linter.style.longLine false in
noncomputable def toThetaPilotArithmeticDivisorLocalEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
      place estimate :=
  source.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    |>.toThetaPilotArithmeticDivisorLocalEvaluationSource

set_option linter.style.longLine false in
def Endpoint
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    Prop :=
  source.arithmeticDivisorSource.Endpoint ∧
    source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.Endpoint ∧
      IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.Endpoint
        source.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource ∧
        IUTStage1IUTIVTheorem110LocalAnalyticArithmeticDivisorEvaluationSource.Endpoint
          source.toLocalAnalyticArithmeticDivisorEvaluationSource ∧
          IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource.Endpoint
            source.toPropositionArithmeticDivisorEvaluationSource ∧
            IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource.Endpoint
              source.toFormulaArithmeticDivisorEvaluationSource ∧
              IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource.Endpoint
                source.toThetaPilotArithmeticDivisorLocalEvaluationSource

set_option linter.style.longLine false in
theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    Endpoint source :=
  ⟨source.arithmeticDivisorSource.endpoint,
    source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.endpoint,
    source.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.endpoint,
    source.toLocalAnalyticArithmeticDivisorEvaluationSource.endpoint,
    source.toPropositionArithmeticDivisorEvaluationSource.endpoint,
    source.toFormulaArithmeticDivisorEvaluationSource.endpoint,
    source.toThetaPilotArithmeticDivisorLocalEvaluationSource.endpoint⟩

set_option linter.style.longLine false in
/--
Source-ingredient audit for the valuation-ball Theorem 1.10 local analytic
boundary.

This expands the single valuation-ball local analytic source into the exact
paper-facing ingredients used downstream: arithmetic divisors, valuation-ball
additive-Haar Proposition 1.4 constructions, additive/local analytic
projections, Proposition/formula projections, the theta-pilot local evaluation,
the Step (vi) zero contribution, and the Step (v)/(vii) formula-to-gap
inequalities.
-/
structure SourceIngredientAudit
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) : Prop where
  arithmeticDivisorEndpoint :
    source.arithmeticDivisorSource.Endpoint
  valuationBallConstructionEndpoint :
    source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.Endpoint
  additiveHaarProjectionEndpoint :
    IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.Endpoint
      source.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
  localAnalyticProjectionEndpoint :
    IUTStage1IUTIVTheorem110LocalAnalyticArithmeticDivisorEvaluationSource.Endpoint
      source.toLocalAnalyticArithmeticDivisorEvaluationSource
  propositionProjectionEndpoint :
    IUTStage1IUTIVTheorem110PropositionArithmeticDivisorEvaluationSource.Endpoint
      source.toPropositionArithmeticDivisorEvaluationSource
  formulaProjectionEndpoint :
    IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource.Endpoint
      source.toFormulaArithmeticDivisorEvaluationSource
  thetaPilotLocalEvaluationEndpoint :
    IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource.Endpoint
      source.toThetaPilotArithmeticDivisorLocalEvaluationSource
  stepV_distinguished_formula_le_gap :
    ∀ placeId : place,
      source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
          placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
        source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.distinguishedProcessionBound
            placeId <=
          source.arithmeticDivisorSource.localArithmeticUpperContribution
              source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId
  stepVI_nondistinguished_zero :
    ∀ placeId : place,
      source.toFormulaArithmeticDivisorEvaluationSource.localCaseFormulaSource.localKind
          placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.nondistinguishedNonarchimedean ->
        source.toFormulaArithmeticDivisorEvaluationSource.localCaseFormulaSource.localProcessionUpperBound
          placeId = 0
  stepVII_archimedean_formula_le_gap :
    ∀ placeId : place,
      source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
          placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
        source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.archimedeanProcessionBound
            placeId <=
          source.arithmeticDivisorSource.localArithmeticUpperContribution
              source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId
  projectedLocalProcessionUpperBound_le_gap :
    ∀ placeId : place,
      source.toFormulaArithmeticDivisorEvaluationSource.localCaseFormulaSource.localProcessionUpperBound
          placeId <=
        source.arithmeticDivisorSource.localArithmeticUpperContribution
            source.toFormulaArithmeticDivisorEvaluationSource.localCaseFormulaSource.localPrimeErrorContribution
              placeId -
          source.toFormulaArithmeticDivisorEvaluationSource.localCaseFormulaSource.localMainLogContribution
            placeId
  endpoint : Endpoint source

set_option linter.style.longLine false in
theorem sourceIngredientAudit
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    SourceIngredientAudit source :=
  { arithmeticDivisorEndpoint :=
      source.arithmeticDivisorSource.endpoint,
    valuationBallConstructionEndpoint :=
      source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.endpoint,
    additiveHaarProjectionEndpoint :=
      source.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.endpoint,
    localAnalyticProjectionEndpoint :=
      source.toLocalAnalyticArithmeticDivisorEvaluationSource.endpoint,
    propositionProjectionEndpoint :=
      source.toPropositionArithmeticDivisorEvaluationSource.endpoint,
    formulaProjectionEndpoint :=
      source.toFormulaArithmeticDivisorEvaluationSource.endpoint,
    thetaPilotLocalEvaluationEndpoint :=
      source.toThetaPilotArithmeticDivisorLocalEvaluationSource.endpoint,
    stepV_distinguished_formula_le_gap :=
      source.distinguished_formula_le_gap,
    stepVI_nondistinguished_zero := by
      intro placeId hkind
      exact
        source.toFormulaArithmeticDivisorEvaluationSource.localCaseFormulaSource
          |>.stepVI_nondistinguished_zero placeId hkind,
    stepVII_archimedean_formula_le_gap :=
      source.archimedean_formula_le_gap,
    projectedLocalProcessionUpperBound_le_gap := by
      intro placeId
      exact
        source.toFormulaArithmeticDivisorEvaluationSource.localCaseFormulaSource
          |>.localProcessionUpperBound_le_gap placeId,
    endpoint := source.endpoint }

end IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
set_option linter.style.longLine true

set_option linter.style.longLine false in
/--
Arithmetic-divisor evaluation source whose valuation-ball local analytic
construction has a selected distinguished nonarchimedean place.

This is the paper-facing p-adic place-selection refinement of the ordinary
valuation-ball local analytic source.  It projects to the existing Theorem
1.10 valuation-ball arithmetic-divisor evaluation source, but additionally
proves that the selected place is distinguished by construction.
-/
structure IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    (place : Type u) [Fintype place]
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (α : Type v) (η : Type w) (K : place -> Type x)
    [∀ placeId : place, TopologicalSpace (K placeId)]
    [∀ placeId : place, MeasurableSpace (K placeId)]
    [∀ placeId : place, AddGroup (K placeId)]
    [∀ placeId : place, T2Space (K placeId)]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (archIndex archSummand : place -> Type v)
    [∀ placeId : place, Fintype (archIndex placeId)]
    [∀ placeId : place, Fintype (archSummand placeId)]
    (selectedDistinguishedPlace : place) where
  arithmeticDivisorSource :
    IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate
  selectedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource :
    IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
      place arithmeticDivisorSource α η K hullSystem archIndex archSummand
      selectedDistinguishedPlace
  distinguished_formula_le_gap :
    ∀ placeId : place,
      selectedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.toValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
          placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean ->
        selectedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.distinguishedProcessionBound
            placeId <=
          arithmeticDivisorSource.localArithmeticUpperContribution
              selectedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            selectedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId
  archimedean_formula_le_gap :
    ∀ placeId : place,
      selectedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.toValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
          placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean ->
        selectedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.archimedeanProcessionBound
            placeId <=
          arithmeticDivisorSource.localArithmeticUpperContribution
              selectedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            selectedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId

namespace IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {α : Type v} {η : Type w} {K : place -> Type x}
variable [∀ placeId : place, TopologicalSpace (K placeId)]
variable [∀ placeId : place, MeasurableSpace (K placeId)]
variable [∀ placeId : place, AddGroup (K placeId)]
variable [∀ placeId : place, T2Space (K placeId)]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {archIndex archSummand : place -> Type v}
variable [∀ placeId : place, Fintype (archIndex placeId)]
variable [∀ placeId : place, Fintype (archSummand placeId)]
variable {selectedDistinguishedPlace : place}

set_option linter.style.longLine false in
noncomputable def toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand
        selectedDistinguishedPlace) :
    IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
      place estimate α η K hullSystem archIndex archSummand :=
  { arithmeticDivisorSource := source.arithmeticDivisorSource,
    valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource :=
      source.selectedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        |>.toValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource,
    distinguished_formula_le_gap :=
      source.distinguished_formula_le_gap,
    archimedean_formula_le_gap :=
      source.archimedean_formula_le_gap }

set_option linter.style.longLine false in
noncomputable def toThetaPilotArithmeticDivisorLocalEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand
        selectedDistinguishedPlace) :
    IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource
      place estimate :=
  source.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    |>.toThetaPilotArithmeticDivisorLocalEvaluationSource

set_option linter.style.longLine false in
theorem selectedDistinguishedPlace_kind
    (source :
      IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand
        selectedDistinguishedPlace) :
    source.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
        selectedDistinguishedPlace =
      IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean :=
  source.selectedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
    |>.selectedDistinguishedPlace_kind

set_option linter.style.longLine false in
def Endpoint
    (source :
      IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand
        selectedDistinguishedPlace) :
    Prop :=
  source.arithmeticDivisorSource.Endpoint ∧
    source.selectedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.Endpoint ∧
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.Endpoint
        source.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource ∧
        IUTStage1IUTIVThetaPilotArithmeticDivisorLocalEvaluationSource.Endpoint
          source.toThetaPilotArithmeticDivisorLocalEvaluationSource

set_option linter.style.longLine false in
theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand
        selectedDistinguishedPlace) :
    Endpoint source :=
  ⟨source.arithmeticDivisorSource.endpoint,
    source.selectedValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.endpoint,
    source.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.endpoint,
    source.toThetaPilotArithmeticDivisorLocalEvaluationSource.endpoint⟩

end IUTStage1IUTIVTheorem110SelectedDistinguishedValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource

set_option linter.style.longLine true

set_option linter.style.longLine false in
/--
Distinguished nonarchimedean formula-to-gap comparison source.

This is the remaining Step (v)/Step (xi) arithmetic comparison at a single
distinguished place.  It ties the local Proposition 1.4 additive-Haar
log-shell construction to the arithmetic-minus-main-log gap used by
Theorem 1.10, rather than passing only the final inequality as an anonymous
field.
-/
structure IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarFormulaGapComparisonSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive)
    (distinguishedProcessionBound localArithmeticMinusMainGap : Real) where
  logShellSource :
    IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound
  formula_bound_le_gap :
    distinguishedProcessionBound <= localArithmeticMinusMainGap

namespace IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarFormulaGapComparisonSource

set_option linter.style.longLine false

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {l : PrimeGeFive}
variable {distinguishedProcessionBound localArithmeticMinusMainGap : Real}

theorem prop14Container_le_gap
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarFormulaGapComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        localArithmeticMinusMainGap) :
    ((source.logShellSource.toDistinguishedLocalLogShellConstructionSource).toDistinguishedLocalLogShellEstimate).prop14ContainerUpperBound <=
      localArithmeticMinusMainGap := by
  exact
    le_trans
      (IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate.prop14_container_le_formula_bound
        (source.logShellSource.toDistinguishedLocalLogShellConstructionSource.toDistinguishedLocalLogShellEstimate))
      source.formula_bound_le_gap

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarFormulaGapComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        localArithmeticMinusMainGap) :
    Prop :=
  source.logShellSource.Endpoint ∧
    distinguishedProcessionBound <= localArithmeticMinusMainGap ∧
      ((source.logShellSource.toDistinguishedLocalLogShellConstructionSource).toDistinguishedLocalLogShellEstimate).prop14ContainerUpperBound <=
        localArithmeticMinusMainGap

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarFormulaGapComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        localArithmeticMinusMainGap) :
    Endpoint source :=
  ⟨source.logShellSource.endpoint, source.formula_bound_le_gap,
    source.prop14Container_le_gap⟩

end IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarFormulaGapComparisonSource

set_option linter.style.longLine false in
/--
Archimedean formula-to-gap comparison source.

This is the Step (vii)/Step (xi) arithmetic comparison at a single archimedean
place.  It keeps the Proposition 1.5 metric construction attached to the final
arithmetic-minus-main-log gap comparison.
-/
structure IUTStage1IUTIVTheorem110ArchimedeanMetricFormulaGapComparisonSource
    (I V : Type u) [Fintype I] [Fintype V]
    (l : PrimeGeFive)
    (archimedeanProcessionBound localArithmeticMinusMainGap : Real) where
  metricSource :
    IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
      I V l archimedeanProcessionBound
  formula_bound_le_gap :
    archimedeanProcessionBound <= localArithmeticMinusMainGap

namespace IUTStage1IUTIVTheorem110ArchimedeanMetricFormulaGapComparisonSource

variable {I V : Type u} [Fintype I] [Fintype V]
variable {l : PrimeGeFive}
variable {archimedeanProcessionBound localArithmeticMinusMainGap : Real}

theorem metricContainer_le_gap
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricFormulaGapComparisonSource
        I V l archimedeanProcessionBound localArithmeticMinusMainGap) :
    source.metricSource.metricContainerLogVolume <=
      localArithmeticMinusMainGap := by
  exact
    le_trans
      (IUTStage1IUTIVProposition15ArchimedeanLocalMetricEstimate.metric_container_le_formula_bound
        source.metricSource.toArchimedeanLocalMetricEstimate)
      source.formula_bound_le_gap

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricFormulaGapComparisonSource
        I V l archimedeanProcessionBound localArithmeticMinusMainGap) :
    Prop :=
  source.metricSource.Endpoint ∧
    archimedeanProcessionBound <= localArithmeticMinusMainGap ∧
      source.metricSource.metricContainerLogVolume <=
        localArithmeticMinusMainGap

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricFormulaGapComparisonSource
        I V l archimedeanProcessionBound localArithmeticMinusMainGap) :
    Endpoint source :=
  ⟨source.metricSource.endpoint, source.formula_bound_le_gap,
    source.metricContainer_le_gap⟩

end IUTStage1IUTIVTheorem110ArchimedeanMetricFormulaGapComparisonSource

set_option linter.style.longLine false in
/--
Distinguished nonarchimedean formula-to-arithmetic-degree comparison source.

This is the sharper Step (v) comparison needed by the Step (xi) corridor: the
Proposition 1.4 additive-Haar log-shell construction is compared directly with
the local arithmetic-degree part \(a_l(D_v+C_v)\), before any prime-error or
main-log terms enter the Theorem 1.10 arithmetic gap.
-/
structure IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDegreeComparisonSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive)
    (distinguishedProcessionBound localArithmeticDegreePart : Real) where
  logShellSource :
    IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound
  formula_bound_le_arithmeticDegreePart :
    distinguishedProcessionBound <= localArithmeticDegreePart

namespace IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDegreeComparisonSource

set_option linter.style.longLine false

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {l : PrimeGeFive}
variable {distinguishedProcessionBound localArithmeticDegreePart : Real}

theorem prop14Container_le_arithmeticDegreePart
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDegreeComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        localArithmeticDegreePart) :
    ((source.logShellSource.toDistinguishedLocalLogShellConstructionSource).toDistinguishedLocalLogShellEstimate).prop14ContainerUpperBound <=
      localArithmeticDegreePart := by
  exact
    le_trans
      (IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate.prop14_container_le_formula_bound
        (source.logShellSource.toDistinguishedLocalLogShellConstructionSource.toDistinguishedLocalLogShellEstimate))
      source.formula_bound_le_arithmeticDegreePart

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDegreeComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        localArithmeticDegreePart) :
    Prop :=
  source.logShellSource.Endpoint ∧
    distinguishedProcessionBound <= localArithmeticDegreePart ∧
      ((source.logShellSource.toDistinguishedLocalLogShellConstructionSource).toDistinguishedLocalLogShellEstimate).prop14ContainerUpperBound <=
        localArithmeticDegreePart

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDegreeComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        localArithmeticDegreePart) :
    Endpoint source :=
  ⟨source.logShellSource.endpoint,
    source.formula_bound_le_arithmeticDegreePart,
    source.prop14Container_le_arithmeticDegreePart⟩

end IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDegreeComparisonSource

set_option linter.style.longLine false in
/--
Archimedean formula-to-arithmetic-degree comparison source.

This is the Step (vii) analogue of the distinguished comparison above: the
Proposition 1.5 metric construction is attached to a direct comparison with
the local arithmetic-degree part \(a_l(D_v+C_v)\).
-/
structure IUTStage1IUTIVTheorem110ArchimedeanMetricArithmeticDegreeComparisonSource
    (I V : Type u) [Fintype I] [Fintype V]
    (l : PrimeGeFive)
    (archimedeanProcessionBound localArithmeticDegreePart : Real) where
  metricSource :
    IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
      I V l archimedeanProcessionBound
  formula_bound_le_arithmeticDegreePart :
    archimedeanProcessionBound <= localArithmeticDegreePart

namespace IUTStage1IUTIVTheorem110ArchimedeanMetricArithmeticDegreeComparisonSource

variable {I V : Type u} [Fintype I] [Fintype V]
variable {l : PrimeGeFive}
variable {archimedeanProcessionBound localArithmeticDegreePart : Real}

theorem metricContainer_le_arithmeticDegreePart
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricArithmeticDegreeComparisonSource
        I V l archimedeanProcessionBound localArithmeticDegreePart) :
    source.metricSource.metricContainerLogVolume <=
      localArithmeticDegreePart := by
  exact
    le_trans
      (IUTStage1IUTIVProposition15ArchimedeanLocalMetricEstimate.metric_container_le_formula_bound
        source.metricSource.toArchimedeanLocalMetricEstimate)
      source.formula_bound_le_arithmeticDegreePart

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricArithmeticDegreeComparisonSource
        I V l archimedeanProcessionBound localArithmeticDegreePart) :
    Prop :=
  source.metricSource.Endpoint ∧
    archimedeanProcessionBound <= localArithmeticDegreePart ∧
      source.metricSource.metricContainerLogVolume <=
        localArithmeticDegreePart

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricArithmeticDegreeComparisonSource
        I V l archimedeanProcessionBound localArithmeticDegreePart) :
    Endpoint source :=
  ⟨source.metricSource.endpoint,
    source.formula_bound_le_arithmeticDegreePart,
    source.metricContainer_le_arithmeticDegreePart⟩

end IUTStage1IUTIVTheorem110ArchimedeanMetricArithmeticDegreeComparisonSource

set_option linter.style.longLine false in
/--
Distinguished arithmetic-degree comparison with calibrated procession bound.

The previous arithmetic-degree comparison source records the final inequality
from the distinguished Step (v) procession formula bound to the local
arithmetic-degree part.  This calibrated version splits that payload into the
two paper-facing assertions: the procession formula bound is the coarse
Step (v) bound produced by the Proposition 1.4/1.7 chain, and that coarse
bound is dominated by \(a_l(D_v+C_v)\).
-/
structure IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarCalibratedArithmeticDegreeComparisonSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive)
    (distinguishedProcessionBound localArithmeticDegreePart : Real) where
  logShellSource :
    IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound
  formula_bound_eq_coarse_procession :
    distinguishedProcessionBound =
      logShellSource.coarseProcessionNormalizedUpperBound
  coarse_procession_le_arithmeticDegreePart :
    logShellSource.coarseProcessionNormalizedUpperBound <=
      localArithmeticDegreePart

namespace
  IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarCalibratedArithmeticDegreeComparisonSource

set_option linter.style.longLine false

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {l : PrimeGeFive}
variable {distinguishedProcessionBound localArithmeticDegreePart : Real}

theorem formula_bound_le_arithmeticDegreePart
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarCalibratedArithmeticDegreeComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        localArithmeticDegreePart) :
    distinguishedProcessionBound <= localArithmeticDegreePart := by
  rw [source.formula_bound_eq_coarse_procession]
  exact source.coarse_procession_le_arithmeticDegreePart

set_option linter.style.longLine false in
def toArithmeticDegreeComparisonSource
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarCalibratedArithmeticDegreeComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        localArithmeticDegreePart) :
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDegreeComparisonSource
      α η K hullSystem l distinguishedProcessionBound
      localArithmeticDegreePart :=
  { logShellSource := source.logShellSource,
    formula_bound_le_arithmeticDegreePart :=
      source.formula_bound_le_arithmeticDegreePart }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarCalibratedArithmeticDegreeComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        localArithmeticDegreePart) :
    Prop :=
  source.logShellSource.Endpoint ∧
    distinguishedProcessionBound =
      source.logShellSource.coarseProcessionNormalizedUpperBound ∧
      source.logShellSource.coarseProcessionNormalizedUpperBound <=
        localArithmeticDegreePart ∧
        source.toArithmeticDegreeComparisonSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarCalibratedArithmeticDegreeComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        localArithmeticDegreePart) :
    Endpoint source :=
  ⟨source.logShellSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.coarse_procession_le_arithmeticDegreePart,
    source.toArithmeticDegreeComparisonSource.endpoint⟩

end IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarCalibratedArithmeticDegreeComparisonSource

set_option linter.style.longLine false in
/--
Archimedean arithmetic-degree comparison with calibrated procession bound.

This is the Step (vii) analogue of the distinguished calibrated comparison:
the archimedean procession formula bound is identified with Lean's coarse
Step (vii) bound, and this coarse bound is compared directly with the local
arithmetic-degree part.
-/
structure IUTStage1IUTIVTheorem110ArchimedeanMetricCalibratedArithmeticDegreeComparisonSource
    (I V : Type u) [Fintype I] [Fintype V]
    (l : PrimeGeFive)
    (archimedeanProcessionBound localArithmeticDegreePart : Real) where
  metricSource :
    IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
      I V l archimedeanProcessionBound
  formula_bound_eq_coarse_procession :
    archimedeanProcessionBound =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l
  coarse_procession_le_arithmeticDegreePart :
    iutIVThetaPilotStepVIIArchimedeanCoarseBound l <=
      localArithmeticDegreePart

namespace IUTStage1IUTIVTheorem110ArchimedeanMetricCalibratedArithmeticDegreeComparisonSource

variable {I V : Type u} [Fintype I] [Fintype V]
variable {l : PrimeGeFive}
variable {archimedeanProcessionBound localArithmeticDegreePart : Real}

theorem formula_bound_le_arithmeticDegreePart
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricCalibratedArithmeticDegreeComparisonSource
        I V l archimedeanProcessionBound localArithmeticDegreePart) :
    archimedeanProcessionBound <= localArithmeticDegreePart := by
  rw [source.formula_bound_eq_coarse_procession]
  exact source.coarse_procession_le_arithmeticDegreePart

def toArithmeticDegreeComparisonSource
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricCalibratedArithmeticDegreeComparisonSource
        I V l archimedeanProcessionBound localArithmeticDegreePart) :
    IUTStage1IUTIVTheorem110ArchimedeanMetricArithmeticDegreeComparisonSource
      I V l archimedeanProcessionBound localArithmeticDegreePart :=
  { metricSource := source.metricSource,
    formula_bound_le_arithmeticDegreePart :=
      source.formula_bound_le_arithmeticDegreePart }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricCalibratedArithmeticDegreeComparisonSource
        I V l archimedeanProcessionBound localArithmeticDegreePart) :
    Prop :=
  source.metricSource.Endpoint ∧
    archimedeanProcessionBound =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l ∧
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l <=
        localArithmeticDegreePart ∧
        source.toArithmeticDegreeComparisonSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricCalibratedArithmeticDegreeComparisonSource
        I V l archimedeanProcessionBound localArithmeticDegreePart) :
    Endpoint source :=
  ⟨source.metricSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.coarse_procession_le_arithmeticDegreePart,
    source.toArithmeticDegreeComparisonSource.endpoint⟩

end IUTStage1IUTIVTheorem110ArchimedeanMetricCalibratedArithmeticDegreeComparisonSource

set_option linter.style.longLine false in
/--
Derived distinguished arithmetic-degree comparison.

This lowers the calibrated comparison one step further.  Instead of assuming
the coarse Step (v) bound is already dominated by \(a_l(D_v+C_v)\), the source
compares it with the unscaled different-plus-conductor degree and then derives
the scaled comparison from \(1 \leq a_l\) and nonnegativity of \(D_v+C_v\).
-/
structure IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarDerivedArithmeticDegreeComparisonSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive)
    (distinguishedProcessionBound arithmeticDegreeCoefficient
      localDifferentDegree localConductorDegree : Real) where
  logShellSource :
    IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound
  formula_bound_eq_coarse_procession :
    distinguishedProcessionBound =
      logShellSource.coarseProcessionNormalizedUpperBound
  arithmeticDegreeCoefficient_ge_one :
    1 <= arithmeticDegreeCoefficient
  localDifferentDegree_nonneg :
    0 <= localDifferentDegree
  localConductorDegree_nonneg :
    0 <= localConductorDegree
  coarse_procession_le_different_conductor_degree :
    logShellSource.coarseProcessionNormalizedUpperBound <=
      localDifferentDegree + localConductorDegree

namespace
  IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarDerivedArithmeticDegreeComparisonSource

set_option linter.style.longLine false

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {l : PrimeGeFive}
variable {distinguishedProcessionBound arithmeticDegreeCoefficient
  localDifferentDegree localConductorDegree : Real}

theorem different_conductor_nonneg
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarDerivedArithmeticDegreeComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    0 <= localDifferentDegree + localConductorDegree :=
  add_nonneg source.localDifferentDegree_nonneg
    source.localConductorDegree_nonneg

theorem different_conductor_le_arithmeticDegreePart
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarDerivedArithmeticDegreeComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    localDifferentDegree + localConductorDegree <=
      arithmeticDegreeCoefficient *
        (localDifferentDegree + localConductorDegree) := by
  have hnonneg := source.different_conductor_nonneg
  have hcoeff := source.arithmeticDegreeCoefficient_ge_one
  nlinarith

theorem coarse_procession_le_arithmeticDegreePart
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarDerivedArithmeticDegreeComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    source.logShellSource.coarseProcessionNormalizedUpperBound <=
      arithmeticDegreeCoefficient *
        (localDifferentDegree + localConductorDegree) :=
  le_trans source.coarse_procession_le_different_conductor_degree
    source.different_conductor_le_arithmeticDegreePart

set_option linter.style.longLine false in
def toCalibratedArithmeticDegreeComparisonSource
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarDerivedArithmeticDegreeComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarCalibratedArithmeticDegreeComparisonSource
      α η K hullSystem l distinguishedProcessionBound
      (arithmeticDegreeCoefficient *
        (localDifferentDegree + localConductorDegree)) :=
  { logShellSource := source.logShellSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    coarse_procession_le_arithmeticDegreePart :=
      source.coarse_procession_le_arithmeticDegreePart }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarDerivedArithmeticDegreeComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    Prop :=
  source.logShellSource.Endpoint ∧
    distinguishedProcessionBound =
      source.logShellSource.coarseProcessionNormalizedUpperBound ∧
      1 <= arithmeticDegreeCoefficient ∧
        0 <= localDifferentDegree ∧
          0 <= localConductorDegree ∧
            source.logShellSource.coarseProcessionNormalizedUpperBound <=
              localDifferentDegree + localConductorDegree ∧
              source.logShellSource.coarseProcessionNormalizedUpperBound <=
                arithmeticDegreeCoefficient *
                  (localDifferentDegree + localConductorDegree) ∧
                source.toCalibratedArithmeticDegreeComparisonSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarDerivedArithmeticDegreeComparisonSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    Endpoint source :=
  ⟨source.logShellSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.arithmeticDegreeCoefficient_ge_one,
    source.localDifferentDegree_nonneg,
    source.localConductorDegree_nonneg,
    source.coarse_procession_le_different_conductor_degree,
    source.coarse_procession_le_arithmeticDegreePart,
    source.toCalibratedArithmeticDegreeComparisonSource.endpoint⟩

end IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarDerivedArithmeticDegreeComparisonSource

set_option linter.style.longLine false in
/--
Derived archimedean arithmetic-degree comparison.

This is the Step (vii) analogue of the distinguished derived comparison: the
coarse archimedean bound is compared with \(D_v+C_v\), then scaled to
\(a_l(D_v+C_v)\) using \(1 \leq a_l\).
-/
structure IUTStage1IUTIVTheorem110ArchimedeanMetricDerivedArithmeticDegreeComparisonSource
    (I V : Type u) [Fintype I] [Fintype V]
    (l : PrimeGeFive)
    (archimedeanProcessionBound arithmeticDegreeCoefficient
      localDifferentDegree localConductorDegree : Real) where
  metricSource :
    IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
      I V l archimedeanProcessionBound
  formula_bound_eq_coarse_procession :
    archimedeanProcessionBound =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l
  arithmeticDegreeCoefficient_ge_one :
    1 <= arithmeticDegreeCoefficient
  localDifferentDegree_nonneg :
    0 <= localDifferentDegree
  localConductorDegree_nonneg :
    0 <= localConductorDegree
  coarse_procession_le_different_conductor_degree :
    iutIVThetaPilotStepVIIArchimedeanCoarseBound l <=
      localDifferentDegree + localConductorDegree

namespace IUTStage1IUTIVTheorem110ArchimedeanMetricDerivedArithmeticDegreeComparisonSource

set_option linter.style.longLine false

variable {I V : Type u} [Fintype I] [Fintype V]
variable {l : PrimeGeFive}
variable {archimedeanProcessionBound arithmeticDegreeCoefficient
  localDifferentDegree localConductorDegree : Real}

theorem different_conductor_nonneg
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricDerivedArithmeticDegreeComparisonSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    0 <= localDifferentDegree + localConductorDegree :=
  add_nonneg source.localDifferentDegree_nonneg
    source.localConductorDegree_nonneg

theorem different_conductor_le_arithmeticDegreePart
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricDerivedArithmeticDegreeComparisonSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    localDifferentDegree + localConductorDegree <=
      arithmeticDegreeCoefficient *
        (localDifferentDegree + localConductorDegree) := by
  have hnonneg := source.different_conductor_nonneg
  have hcoeff := source.arithmeticDegreeCoefficient_ge_one
  nlinarith

theorem coarse_procession_le_arithmeticDegreePart
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricDerivedArithmeticDegreeComparisonSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    iutIVThetaPilotStepVIIArchimedeanCoarseBound l <=
      arithmeticDegreeCoefficient *
        (localDifferentDegree + localConductorDegree) :=
  le_trans source.coarse_procession_le_different_conductor_degree
    source.different_conductor_le_arithmeticDegreePart

def toCalibratedArithmeticDegreeComparisonSource
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricDerivedArithmeticDegreeComparisonSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    IUTStage1IUTIVTheorem110ArchimedeanMetricCalibratedArithmeticDegreeComparisonSource
      I V l archimedeanProcessionBound
      (arithmeticDegreeCoefficient *
        (localDifferentDegree + localConductorDegree)) :=
  { metricSource := source.metricSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    coarse_procession_le_arithmeticDegreePart :=
      source.coarse_procession_le_arithmeticDegreePart }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricDerivedArithmeticDegreeComparisonSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    Prop :=
  source.metricSource.Endpoint ∧
    archimedeanProcessionBound =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l ∧
      1 <= arithmeticDegreeCoefficient ∧
        0 <= localDifferentDegree ∧
          0 <= localConductorDegree ∧
            iutIVThetaPilotStepVIIArchimedeanCoarseBound l <=
              localDifferentDegree + localConductorDegree ∧
              iutIVThetaPilotStepVIIArchimedeanCoarseBound l <=
                arithmeticDegreeCoefficient *
                  (localDifferentDegree + localConductorDegree) ∧
                source.toCalibratedArithmeticDegreeComparisonSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricDerivedArithmeticDegreeComparisonSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    Endpoint source :=
  ⟨source.metricSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.arithmeticDegreeCoefficient_ge_one,
    source.localDifferentDegree_nonneg,
    source.localConductorDegree_nonneg,
    source.coarse_procession_le_different_conductor_degree,
    source.coarse_procession_le_arithmeticDegreePart,
    source.toCalibratedArithmeticDegreeComparisonSource.endpoint⟩

end IUTStage1IUTIVTheorem110ArchimedeanMetricDerivedArithmeticDegreeComparisonSource

set_option linter.style.longLine false in
/--
Distinguished unscaled local degree-bound source.

This is the local paper-facing payload immediately below the derived
arithmetic-degree comparison.  It names the Proposition 1.4 tensor bound as the
unscaled different-plus-conductor degree bound and derives the comparison
`coarse <= D + C` from that named local degree comparison.
-/
structure IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeBoundSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive)
    (distinguishedProcessionBound arithmeticDegreeCoefficient
      localDifferentDegree localConductorDegree : Real) where
  logShellSource :
    IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound
  formula_bound_eq_coarse_procession :
    distinguishedProcessionBound =
      logShellSource.coarseProcessionNormalizedUpperBound
  arithmeticDegreeCoefficient_ge_one :
    1 <= arithmeticDegreeCoefficient
  localDifferentDegree_nonneg :
    0 <= localDifferentDegree
  localConductorDegree_nonneg :
    0 <= localConductorDegree
  prop14DegreeBound : Real
  prop14_degreeBound_eq_tensorFormula :
    prop14DegreeBound =
      iutIVProp14DistinguishedTensorBound
        logShellSource.additiveHaarSource.residuePrime
        logShellSource.lambda logShellSource.dI
        logShellSource.exceptionalRamificationLogSum
  prop14_degreeBound_eq_different_conductor :
    prop14DegreeBound = localDifferentDegree + localConductorDegree
  stepV_coarse_le_prop14_degreeBound :
    logShellSource.coarseProcessionNormalizedUpperBound <= prop14DegreeBound

namespace
  IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeBoundSource

set_option linter.style.longLine false

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {l : PrimeGeFive}
variable {distinguishedProcessionBound arithmeticDegreeCoefficient
  localDifferentDegree localConductorDegree : Real}

theorem coarse_procession_le_different_conductor_degree
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeBoundSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    source.logShellSource.coarseProcessionNormalizedUpperBound <=
      localDifferentDegree + localConductorDegree := by
  rw [← source.prop14_degreeBound_eq_different_conductor]
  exact source.stepV_coarse_le_prop14_degreeBound

set_option linter.style.longLine false in
def toDerivedArithmeticDegreeComparisonSource
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeBoundSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarDerivedArithmeticDegreeComparisonSource
      α η K hullSystem l distinguishedProcessionBound
      arithmeticDegreeCoefficient localDifferentDegree localConductorDegree :=
  { logShellSource := source.logShellSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    localDifferentDegree_nonneg :=
      source.localDifferentDegree_nonneg,
    localConductorDegree_nonneg :=
      source.localConductorDegree_nonneg,
    coarse_procession_le_different_conductor_degree :=
      source.coarse_procession_le_different_conductor_degree }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeBoundSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    Prop :=
  source.logShellSource.Endpoint ∧
    distinguishedProcessionBound =
      source.logShellSource.coarseProcessionNormalizedUpperBound ∧
      1 <= arithmeticDegreeCoefficient ∧
        0 <= localDifferentDegree ∧
          0 <= localConductorDegree ∧
            source.prop14DegreeBound =
              iutIVProp14DistinguishedTensorBound
                source.logShellSource.additiveHaarSource.residuePrime
                source.logShellSource.lambda source.logShellSource.dI
                source.logShellSource.exceptionalRamificationLogSum ∧
              source.prop14DegreeBound =
                localDifferentDegree + localConductorDegree ∧
                source.logShellSource.coarseProcessionNormalizedUpperBound <=
                  source.prop14DegreeBound ∧
                  source.logShellSource.coarseProcessionNormalizedUpperBound <=
                    localDifferentDegree + localConductorDegree ∧
                    source.toDerivedArithmeticDegreeComparisonSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeBoundSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    Endpoint source :=
  ⟨source.logShellSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.arithmeticDegreeCoefficient_ge_one,
    source.localDifferentDegree_nonneg,
    source.localConductorDegree_nonneg,
    source.prop14_degreeBound_eq_tensorFormula,
    source.prop14_degreeBound_eq_different_conductor,
    source.stepV_coarse_le_prop14_degreeBound,
    source.coarse_procession_le_different_conductor_degree,
    source.toDerivedArithmeticDegreeComparisonSource.endpoint⟩

end IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeBoundSource

set_option linter.style.longLine false in
/--
Distinguished local degree-identification source below the unscaled
Theorem 1.10 arithmetic-degree comparison.

This isolates the remaining paper-side local matching assertion: the
Proposition 1.4 tensor expression
`-\lambda + d_I + 4 log(p) + Ram` is identified with the local
different-plus-conductor degree `D_v + C_v`, and the coarse Step (v)
procession bound is dominated by this identified degree.  The constructor below
then produces the unscaled degree-bound source; nonnegativity and the
arithmetic-degree coefficient lower bound stay explicit local arithmetic data.
-/
structure IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeIdentificationSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive)
    (distinguishedProcessionBound arithmeticDegreeCoefficient
      localDifferentDegree localConductorDegree : Real) where
  logShellSource :
    IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound
  formula_bound_eq_coarse_procession :
    distinguishedProcessionBound =
      logShellSource.coarseProcessionNormalizedUpperBound
  arithmeticDegreeCoefficient_ge_one :
    1 <= arithmeticDegreeCoefficient
  localDifferentDegree_nonneg :
    0 <= localDifferentDegree
  localConductorDegree_nonneg :
    0 <= localConductorDegree
  tensorFormula_eq_different_conductor :
    iutIVProp14DistinguishedTensorBound
        logShellSource.additiveHaarSource.residuePrime
        logShellSource.lambda logShellSource.dI
        logShellSource.exceptionalRamificationLogSum =
      localDifferentDegree + localConductorDegree
  coarse_procession_le_tensorFormula :
    logShellSource.coarseProcessionNormalizedUpperBound <=
      iutIVProp14DistinguishedTensorBound
        logShellSource.additiveHaarSource.residuePrime
        logShellSource.lambda logShellSource.dI
        logShellSource.exceptionalRamificationLogSum

namespace
  IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeIdentificationSource

set_option linter.style.longLine false

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {l : PrimeGeFive}
variable {distinguishedProcessionBound arithmeticDegreeCoefficient
  localDifferentDegree localConductorDegree : Real}

theorem coarse_procession_le_different_conductor_degree
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeIdentificationSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    source.logShellSource.coarseProcessionNormalizedUpperBound <=
      localDifferentDegree + localConductorDegree := by
  rw [← source.tensorFormula_eq_different_conductor]
  exact source.coarse_procession_le_tensorFormula

set_option linter.style.longLine false in
noncomputable def toUnscaledDegreeBoundSource
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeIdentificationSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeBoundSource
      α η K hullSystem l distinguishedProcessionBound
      arithmeticDegreeCoefficient localDifferentDegree localConductorDegree :=
  { logShellSource := source.logShellSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    localDifferentDegree_nonneg :=
      source.localDifferentDegree_nonneg,
    localConductorDegree_nonneg :=
      source.localConductorDegree_nonneg,
    prop14DegreeBound :=
      iutIVProp14DistinguishedTensorBound
        source.logShellSource.additiveHaarSource.residuePrime
        source.logShellSource.lambda source.logShellSource.dI
        source.logShellSource.exceptionalRamificationLogSum,
    prop14_degreeBound_eq_tensorFormula := rfl,
    prop14_degreeBound_eq_different_conductor :=
      source.tensorFormula_eq_different_conductor,
    stepV_coarse_le_prop14_degreeBound :=
      source.coarse_procession_le_tensorFormula }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeIdentificationSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    Prop :=
  source.logShellSource.Endpoint ∧
    distinguishedProcessionBound =
      source.logShellSource.coarseProcessionNormalizedUpperBound ∧
      1 <= arithmeticDegreeCoefficient ∧
        0 <= localDifferentDegree ∧
          0 <= localConductorDegree ∧
            iutIVProp14DistinguishedTensorBound
                source.logShellSource.additiveHaarSource.residuePrime
                source.logShellSource.lambda source.logShellSource.dI
                source.logShellSource.exceptionalRamificationLogSum =
              localDifferentDegree + localConductorDegree ∧
              source.logShellSource.coarseProcessionNormalizedUpperBound <=
                iutIVProp14DistinguishedTensorBound
                  source.logShellSource.additiveHaarSource.residuePrime
                  source.logShellSource.lambda source.logShellSource.dI
                  source.logShellSource.exceptionalRamificationLogSum ∧
                source.logShellSource.coarseProcessionNormalizedUpperBound <=
                  localDifferentDegree + localConductorDegree ∧
                  source.toUnscaledDegreeBoundSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeIdentificationSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    Endpoint source :=
  ⟨source.logShellSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.arithmeticDegreeCoefficient_ge_one,
    source.localDifferentDegree_nonneg,
    source.localConductorDegree_nonneg,
    source.tensorFormula_eq_different_conductor,
    source.coarse_procession_le_tensorFormula,
    source.coarse_procession_le_different_conductor_degree,
    source.toUnscaledDegreeBoundSource.endpoint⟩

end IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeIdentificationSource

set_option linter.style.longLine false in
/--
Distinguished tensor-degree component source for Theorem 1.10, Step (v).

This lowers the distinguished local degree-identification object by splitting
the equality
`-\lambda + d_I + 4 log(p) + Ram = D_v + C_v` into its two paper-side
components: the local different contribution is the non-conductor part
`-\lambda + d_I + Ram`, while the local conductor contribution is the
`4 log(p)` term produced by the integral-power rounding in Proposition 1.4.
-/
structure IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarTensorDegreeComponentSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive)
    (distinguishedProcessionBound arithmeticDegreeCoefficient
      localDifferentDegree localConductorDegree : Real) where
  logShellSource :
    IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound
  formula_bound_eq_coarse_procession :
    distinguishedProcessionBound =
      logShellSource.coarseProcessionNormalizedUpperBound
  arithmeticDegreeCoefficient_ge_one :
    1 <= arithmeticDegreeCoefficient
  localDifferentDegree_nonneg :
    0 <= localDifferentDegree
  localConductorDegree_nonneg :
    0 <= localConductorDegree
  localDifferentDegree_eq_tensorDifferentPart :
    localDifferentDegree =
      -logShellSource.lambda + logShellSource.dI +
        logShellSource.exceptionalRamificationLogSum
  localConductorDegree_eq_tensorConductorPart :
    localConductorDegree =
      4 * Real.log (logShellSource.additiveHaarSource.residuePrime : Real)
  coarse_procession_le_tensorFormula :
    logShellSource.coarseProcessionNormalizedUpperBound <=
      iutIVProp14DistinguishedTensorBound
        logShellSource.additiveHaarSource.residuePrime
        logShellSource.lambda logShellSource.dI
        logShellSource.exceptionalRamificationLogSum

namespace IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarTensorDegreeComponentSource

set_option linter.style.longLine false

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {l : PrimeGeFive}
variable {distinguishedProcessionBound arithmeticDegreeCoefficient
  localDifferentDegree localConductorDegree : Real}

theorem tensorFormula_eq_different_conductor
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    iutIVProp14DistinguishedTensorBound
        source.logShellSource.additiveHaarSource.residuePrime
        source.logShellSource.lambda source.logShellSource.dI
        source.logShellSource.exceptionalRamificationLogSum =
      localDifferentDegree + localConductorDegree := by
  calc
    iutIVProp14DistinguishedTensorBound
        source.logShellSource.additiveHaarSource.residuePrime
        source.logShellSource.lambda source.logShellSource.dI
        source.logShellSource.exceptionalRamificationLogSum =
      (-source.logShellSource.lambda + source.logShellSource.dI +
          source.logShellSource.exceptionalRamificationLogSum) +
        4 * Real.log
          (source.logShellSource.additiveHaarSource.residuePrime : Real) := by
      rw [iutIVProp14DistinguishedTensorBound]
      ring_nf
    _ = localDifferentDegree + localConductorDegree := by
      rw [← source.localDifferentDegree_eq_tensorDifferentPart,
        ← source.localConductorDegree_eq_tensorConductorPart]

set_option linter.style.longLine false in
noncomputable def toUnscaledDegreeIdentificationSource
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeIdentificationSource
      α η K hullSystem l distinguishedProcessionBound
      arithmeticDegreeCoefficient localDifferentDegree localConductorDegree :=
  { logShellSource := source.logShellSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    localDifferentDegree_nonneg :=
      source.localDifferentDegree_nonneg,
    localConductorDegree_nonneg :=
      source.localConductorDegree_nonneg,
    tensorFormula_eq_different_conductor :=
      source.tensorFormula_eq_different_conductor,
    coarse_procession_le_tensorFormula :=
      source.coarse_procession_le_tensorFormula }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    Prop :=
  source.logShellSource.Endpoint ∧
    distinguishedProcessionBound =
      source.logShellSource.coarseProcessionNormalizedUpperBound ∧
      1 <= arithmeticDegreeCoefficient ∧
        0 <= localDifferentDegree ∧
          0 <= localConductorDegree ∧
            localDifferentDegree =
              -source.logShellSource.lambda + source.logShellSource.dI +
                source.logShellSource.exceptionalRamificationLogSum ∧
              localConductorDegree =
                4 * Real.log
                  (source.logShellSource.additiveHaarSource.residuePrime : Real) ∧
                iutIVProp14DistinguishedTensorBound
                    source.logShellSource.additiveHaarSource.residuePrime
                    source.logShellSource.lambda source.logShellSource.dI
                    source.logShellSource.exceptionalRamificationLogSum =
                  localDifferentDegree + localConductorDegree ∧
                  source.logShellSource.coarseProcessionNormalizedUpperBound <=
                    iutIVProp14DistinguishedTensorBound
                      source.logShellSource.additiveHaarSource.residuePrime
                      source.logShellSource.lambda source.logShellSource.dI
                      source.logShellSource.exceptionalRamificationLogSum ∧
                    source.toUnscaledDegreeIdentificationSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient localDifferentDegree
        localConductorDegree) :
    Endpoint source :=
  ⟨source.logShellSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.arithmeticDegreeCoefficient_ge_one,
    source.localDifferentDegree_nonneg,
    source.localConductorDegree_nonneg,
    source.localDifferentDegree_eq_tensorDifferentPart,
    source.localConductorDegree_eq_tensorConductorPart,
    source.tensorFormula_eq_different_conductor,
    source.coarse_procession_le_tensorFormula,
    source.toUnscaledDegreeIdentificationSource.endpoint⟩

end IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarTensorDegreeComponentSource

set_option linter.style.longLine false in
/--
Constructed distinguished tensor-degree component source.

This is the finite-place analogue of the constructed archimedean metric
component source.  The local different component is defined to be the
non-conductor tensor contribution
`-\lambda + d_I + Ram`, and the local conductor component is defined to be the
`4 log(p)` conductor contribution in Proposition 1.4.  Thus the component
equalities of
`IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarTensorDegreeComponentSource`
are no longer supplied as arbitrary fields.
-/
structure IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive)
    (distinguishedProcessionBound arithmeticDegreeCoefficient : Real) where
  logShellSource :
    IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound
  formula_bound_eq_coarse_procession :
    distinguishedProcessionBound =
      logShellSource.coarseProcessionNormalizedUpperBound
  arithmeticDegreeCoefficient_ge_one :
    1 <= arithmeticDegreeCoefficient
  tensorDifferentPart_nonneg :
    0 <= -logShellSource.lambda + logShellSource.dI +
      logShellSource.exceptionalRamificationLogSum
  coarse_procession_le_tensorFormula :
    logShellSource.coarseProcessionNormalizedUpperBound <=
      iutIVProp14DistinguishedTensorBound
        logShellSource.additiveHaarSource.residuePrime
        logShellSource.lambda logShellSource.dI
        logShellSource.exceptionalRamificationLogSum

namespace IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource

set_option linter.style.longLine false

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {l : PrimeGeFive}
variable {distinguishedProcessionBound arithmeticDegreeCoefficient : Real}

noncomputable def localDifferentDegree
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient) :
    Real :=
  -source.logShellSource.lambda + source.logShellSource.dI +
    source.logShellSource.exceptionalRamificationLogSum

noncomputable def localConductorDegree
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient) :
    Real :=
  4 * Real.log (source.logShellSource.additiveHaarSource.residuePrime : Real)

theorem localDifferentDegree_nonneg
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient) :
    0 <= source.localDifferentDegree := by
  simpa [localDifferentDegree] using source.tensorDifferentPart_nonneg

theorem localConductorDegree_nonneg
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient) :
    0 <= source.localConductorDegree := by
  dsimp [localConductorDegree]
  have hp1 :
      (1 : Real) <=
        (source.logShellSource.additiveHaarSource.residuePrime : Real) := by
    exact_mod_cast
      source.logShellSource.additiveHaarSource.residue_prime.one_le
  have hlog :
      0 <= Real.log
        (source.logShellSource.additiveHaarSource.residuePrime : Real) :=
    Real.log_nonneg hp1
  nlinarith

set_option linter.style.longLine false in
noncomputable def toTensorDegreeComponentSource
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient) :
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarTensorDegreeComponentSource
      α η K hullSystem l distinguishedProcessionBound
      arithmeticDegreeCoefficient source.localDifferentDegree
      source.localConductorDegree :=
  { logShellSource := source.logShellSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    localDifferentDegree_nonneg :=
      source.localDifferentDegree_nonneg,
    localConductorDegree_nonneg :=
      source.localConductorDegree_nonneg,
    localDifferentDegree_eq_tensorDifferentPart := by
      rfl,
    localConductorDegree_eq_tensorConductorPart := by
      rfl,
    coarse_procession_le_tensorFormula :=
      source.coarse_procession_le_tensorFormula }

set_option linter.style.longLine false in
noncomputable def toUnscaledDegreeIdentificationSource
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient) :
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarUnscaledDegreeIdentificationSource
      α η K hullSystem l distinguishedProcessionBound
      arithmeticDegreeCoefficient source.localDifferentDegree
      source.localConductorDegree :=
  source.toTensorDegreeComponentSource.toUnscaledDegreeIdentificationSource

set_option linter.style.longLine false in
noncomputable def toCalibratedTensorDegreeComponentSource
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient)
    (localDifferentDegree localConductorDegree : Real)
    (localDifferentDegree_eq_constructed :
      localDifferentDegree = source.localDifferentDegree)
    (localConductorDegree_eq_constructed :
      localConductorDegree = source.localConductorDegree) :
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarTensorDegreeComponentSource
      α η K hullSystem l distinguishedProcessionBound
      arithmeticDegreeCoefficient localDifferentDegree localConductorDegree :=
  { logShellSource := source.logShellSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    localDifferentDegree_nonneg := by
      rw [localDifferentDegree_eq_constructed]
      exact source.localDifferentDegree_nonneg,
    localConductorDegree_nonneg := by
      rw [localConductorDegree_eq_constructed]
      exact source.localConductorDegree_nonneg,
    localDifferentDegree_eq_tensorDifferentPart := by
      rw [localDifferentDegree_eq_constructed]
      rfl,
    localConductorDegree_eq_tensorConductorPart := by
      rw [localConductorDegree_eq_constructed]
      rfl,
    coarse_procession_le_tensorFormula :=
      source.coarse_procession_le_tensorFormula }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient) :
    Prop :=
  source.logShellSource.Endpoint ∧
    distinguishedProcessionBound =
      source.logShellSource.coarseProcessionNormalizedUpperBound ∧
      1 <= arithmeticDegreeCoefficient ∧
        0 <= source.localDifferentDegree ∧
          0 <= source.localConductorDegree ∧
            source.logShellSource.coarseProcessionNormalizedUpperBound <=
              iutIVProp14DistinguishedTensorBound
                source.logShellSource.additiveHaarSource.residuePrime
                source.logShellSource.lambda source.logShellSource.dI
                source.logShellSource.exceptionalRamificationLogSum ∧
              source.toTensorDegreeComponentSource.Endpoint ∧
                source.toUnscaledDegreeIdentificationSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient) :
    Endpoint source :=
  ⟨source.logShellSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.arithmeticDegreeCoefficient_ge_one,
    source.localDifferentDegree_nonneg,
    source.localConductorDegree_nonneg,
    source.coarse_procession_le_tensorFormula,
    source.toTensorDegreeComponentSource.endpoint,
    source.toUnscaledDegreeIdentificationSource.endpoint⟩

def CalibratedEndpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient)
    (localDifferentDegree localConductorDegree : Real)
    (localDifferentDegree_eq_constructed :
      localDifferentDegree = source.localDifferentDegree)
    (localConductorDegree_eq_constructed :
      localConductorDegree = source.localConductorDegree) :
    Prop :=
  source.Endpoint ∧
    0 <= localDifferentDegree ∧
      0 <= localConductorDegree ∧
        (source.toCalibratedTensorDegreeComponentSource
          localDifferentDegree localConductorDegree
          localDifferentDegree_eq_constructed
          localConductorDegree_eq_constructed).Endpoint

theorem calibratedEndpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient)
    (localDifferentDegree localConductorDegree : Real)
    (localDifferentDegree_eq_constructed :
      localDifferentDegree = source.localDifferentDegree)
    (localConductorDegree_eq_constructed :
      localConductorDegree = source.localConductorDegree) :
    CalibratedEndpoint source localDifferentDegree localConductorDegree
      localDifferentDegree_eq_constructed
      localConductorDegree_eq_constructed := by
  refine ⟨source.endpoint, ?_, ?_, ?_⟩
  · rw [localDifferentDegree_eq_constructed]
    exact source.localDifferentDegree_nonneg
  · rw [localConductorDegree_eq_constructed]
    exact source.localConductorDegree_nonneg
  · exact
      (source.toCalibratedTensorDegreeComponentSource
        localDifferentDegree localConductorDegree
        localDifferentDegree_eq_constructed
        localConductorDegree_eq_constructed).endpoint

end IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource

set_option linter.style.longLine false in
/--
Constructed distinguished tensor-degree component source backed by the
effective arithmetic different divisor.

The previous constructed tensor component still needed nonnegativity of the
paper expression `-\lambda + d_I + Ram` as a direct field.  This source lowers
that payload to the arithmetic-divisor side of Definition 1.9/Theorem 1.10:
the local different degree is known nonnegative by effectivity of the different
divisor, and is identified with the Proposition 1.4 tensor-different term.
-/
structure IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConstructedTensorDegreeComponentSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive)
    (distinguishedProcessionBound arithmeticDegreeCoefficient
      arithmeticLocalDifferentDegree : Real) where
  logShellSource :
    IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound
  formula_bound_eq_coarse_procession :
    distinguishedProcessionBound =
      logShellSource.coarseProcessionNormalizedUpperBound
  arithmeticDegreeCoefficient_ge_one :
    1 <= arithmeticDegreeCoefficient
  arithmeticLocalDifferentDegree_nonneg :
    0 <= arithmeticLocalDifferentDegree
  arithmeticLocalDifferentDegree_eq_tensorDifferentPart :
    arithmeticLocalDifferentDegree =
      -logShellSource.lambda + logShellSource.dI +
        logShellSource.exceptionalRamificationLogSum
  coarse_procession_le_tensorFormula :
    logShellSource.coarseProcessionNormalizedUpperBound <=
      iutIVProp14DistinguishedTensorBound
        logShellSource.additiveHaarSource.residuePrime
        logShellSource.lambda logShellSource.dI
        logShellSource.exceptionalRamificationLogSum

namespace IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConstructedTensorDegreeComponentSource

set_option linter.style.longLine false

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {l : PrimeGeFive}
variable {distinguishedProcessionBound arithmeticDegreeCoefficient
  arithmeticLocalDifferentDegree : Real}

theorem tensorDifferentPart_nonneg
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient arithmeticLocalDifferentDegree) :
    0 <= -source.logShellSource.lambda + source.logShellSource.dI +
      source.logShellSource.exceptionalRamificationLogSum := by
  rw [← source.arithmeticLocalDifferentDegree_eq_tensorDifferentPart]
  exact source.arithmeticLocalDifferentDegree_nonneg

set_option linter.style.longLine false in
noncomputable def toConstructedTensorDegreeComponentSource
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient arithmeticLocalDifferentDegree) :
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
      α η K hullSystem l distinguishedProcessionBound
      arithmeticDegreeCoefficient :=
  { logShellSource := source.logShellSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    tensorDifferentPart_nonneg :=
      source.tensorDifferentPart_nonneg,
    coarse_procession_le_tensorFormula :=
      source.coarse_procession_le_tensorFormula }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient arithmeticLocalDifferentDegree) :
    Prop :=
  source.logShellSource.Endpoint ∧
    distinguishedProcessionBound =
      source.logShellSource.coarseProcessionNormalizedUpperBound ∧
      1 <= arithmeticDegreeCoefficient ∧
        0 <= arithmeticLocalDifferentDegree ∧
          arithmeticLocalDifferentDegree =
            -source.logShellSource.lambda + source.logShellSource.dI +
              source.logShellSource.exceptionalRamificationLogSum ∧
            0 <= -source.logShellSource.lambda + source.logShellSource.dI +
              source.logShellSource.exceptionalRamificationLogSum ∧
              source.logShellSource.coarseProcessionNormalizedUpperBound <=
                iutIVProp14DistinguishedTensorBound
                  source.logShellSource.additiveHaarSource.residuePrime
                  source.logShellSource.lambda source.logShellSource.dI
                  source.logShellSource.exceptionalRamificationLogSum ∧
                source.toConstructedTensorDegreeComponentSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient arithmeticLocalDifferentDegree) :
    Endpoint source :=
  ⟨source.logShellSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.arithmeticDegreeCoefficient_ge_one,
    source.arithmeticLocalDifferentDegree_nonneg,
    source.arithmeticLocalDifferentDegree_eq_tensorDifferentPart,
    source.tensorDifferentPart_nonneg,
    source.coarse_procession_le_tensorFormula,
    source.toConstructedTensorDegreeComponentSource.endpoint⟩

end IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConstructedTensorDegreeComponentSource

set_option linter.style.longLine false in
/--
Constructed distinguished tensor-degree component source backed by effective
arithmetic different and conductor divisors.

This lowers the finite component one step past the effective-different source:
the local conductor degree is also supplied from the arithmetic-divisor side and
identified with the Proposition 1.4 conductor term `4 log(p)`.  Thus the
finite component no longer exposes a separate conductor-calibration equality to
the public matched-local-degree source.
-/
structure IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConductorConstructedTensorDegreeComponentSource
    (α : Type u) (η : Type v) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive)
    (distinguishedProcessionBound arithmeticDegreeCoefficient
      arithmeticLocalDifferentDegree arithmeticLocalConductorDegree : Real) where
  logShellSource :
    IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound
  formula_bound_eq_coarse_procession :
    distinguishedProcessionBound =
      logShellSource.coarseProcessionNormalizedUpperBound
  arithmeticDegreeCoefficient_ge_one :
    1 <= arithmeticDegreeCoefficient
  arithmeticLocalDifferentDegree_nonneg :
    0 <= arithmeticLocalDifferentDegree
  arithmeticLocalConductorDegree_nonneg :
    0 <= arithmeticLocalConductorDegree
  arithmeticLocalDifferentDegree_eq_tensorDifferentPart :
    arithmeticLocalDifferentDegree =
      -logShellSource.lambda + logShellSource.dI +
        logShellSource.exceptionalRamificationLogSum
  arithmeticLocalConductorDegree_eq_tensorConductorPart :
    arithmeticLocalConductorDegree =
      4 * Real.log (logShellSource.additiveHaarSource.residuePrime : Real)
  coarse_procession_le_tensorFormula :
    logShellSource.coarseProcessionNormalizedUpperBound <=
      iutIVProp14DistinguishedTensorBound
        logShellSource.additiveHaarSource.residuePrime
        logShellSource.lambda logShellSource.dI
        logShellSource.exceptionalRamificationLogSum

namespace IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConductorConstructedTensorDegreeComponentSource

set_option linter.style.longLine false

variable {α : Type u} {η : Type v} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {l : PrimeGeFive}
variable {distinguishedProcessionBound arithmeticDegreeCoefficient
  arithmeticLocalDifferentDegree arithmeticLocalConductorDegree : Real}

set_option linter.style.longLine false in
noncomputable def toEffectiveDifferentConstructedTensorDegreeComponentSource
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConductorConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient arithmeticLocalDifferentDegree
        arithmeticLocalConductorDegree) :
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConstructedTensorDegreeComponentSource
      α η K hullSystem l distinguishedProcessionBound
      arithmeticDegreeCoefficient arithmeticLocalDifferentDegree :=
  { logShellSource := source.logShellSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    arithmeticLocalDifferentDegree_nonneg :=
      source.arithmeticLocalDifferentDegree_nonneg,
    arithmeticLocalDifferentDegree_eq_tensorDifferentPart :=
      source.arithmeticLocalDifferentDegree_eq_tensorDifferentPart,
    coarse_procession_le_tensorFormula :=
      source.coarse_procession_le_tensorFormula }

set_option linter.style.longLine false in
noncomputable def toConstructedTensorDegreeComponentSource
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConductorConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient arithmeticLocalDifferentDegree
        arithmeticLocalConductorDegree) :
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
      α η K hullSystem l distinguishedProcessionBound
      arithmeticDegreeCoefficient :=
  source.toEffectiveDifferentConstructedTensorDegreeComponentSource
    |>.toConstructedTensorDegreeComponentSource

theorem arithmeticLocalDifferentDegree_eq_constructed
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConductorConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient arithmeticLocalDifferentDegree
        arithmeticLocalConductorDegree) :
    arithmeticLocalDifferentDegree =
      source.toConstructedTensorDegreeComponentSource.localDifferentDegree := by
  simpa [
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource.localDifferentDegree,
    toConstructedTensorDegreeComponentSource,
    toEffectiveDifferentConstructedTensorDegreeComponentSource,
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConstructedTensorDegreeComponentSource.toConstructedTensorDegreeComponentSource]
    using source.arithmeticLocalDifferentDegree_eq_tensorDifferentPart

theorem arithmeticLocalConductorDegree_eq_constructed
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConductorConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient arithmeticLocalDifferentDegree
        arithmeticLocalConductorDegree) :
    arithmeticLocalConductorDegree =
      source.toConstructedTensorDegreeComponentSource.localConductorDegree := by
  simpa [
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource.localConductorDegree,
    toConstructedTensorDegreeComponentSource,
    toEffectiveDifferentConstructedTensorDegreeComponentSource,
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConstructedTensorDegreeComponentSource.toConstructedTensorDegreeComponentSource]
    using source.arithmeticLocalConductorDegree_eq_tensorConductorPart

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConductorConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient arithmeticLocalDifferentDegree
        arithmeticLocalConductorDegree) :
    Prop :=
  source.logShellSource.Endpoint ∧
    distinguishedProcessionBound =
      source.logShellSource.coarseProcessionNormalizedUpperBound ∧
      1 <= arithmeticDegreeCoefficient ∧
        0 <= arithmeticLocalDifferentDegree ∧
          0 <= arithmeticLocalConductorDegree ∧
            arithmeticLocalDifferentDegree =
              -source.logShellSource.lambda + source.logShellSource.dI +
                source.logShellSource.exceptionalRamificationLogSum ∧
              arithmeticLocalConductorDegree =
                4 * Real.log
                  (source.logShellSource.additiveHaarSource.residuePrime : Real) ∧
                source.logShellSource.coarseProcessionNormalizedUpperBound <=
                  iutIVProp14DistinguishedTensorBound
                    source.logShellSource.additiveHaarSource.residuePrime
                    source.logShellSource.lambda source.logShellSource.dI
                    source.logShellSource.exceptionalRamificationLogSum ∧
                  source.toEffectiveDifferentConstructedTensorDegreeComponentSource.Endpoint ∧
                    source.toConstructedTensorDegreeComponentSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConductorConstructedTensorDegreeComponentSource
        α η K hullSystem l distinguishedProcessionBound
        arithmeticDegreeCoefficient arithmeticLocalDifferentDegree
        arithmeticLocalConductorDegree) :
    Endpoint source :=
  ⟨source.logShellSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.arithmeticDegreeCoefficient_ge_one,
    source.arithmeticLocalDifferentDegree_nonneg,
    source.arithmeticLocalConductorDegree_nonneg,
    source.arithmeticLocalDifferentDegree_eq_tensorDifferentPart,
    source.arithmeticLocalConductorDegree_eq_tensorConductorPart,
    source.coarse_procession_le_tensorFormula,
    source.toEffectiveDifferentConstructedTensorDegreeComponentSource.endpoint,
    source.toConstructedTensorDegreeComponentSource.endpoint⟩

end IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConductorConstructedTensorDegreeComponentSource

set_option linter.style.longLine false in
/--
Distinguished tensor-degree component source backed by the arithmetic divisors
of Definition 1.9 / Theorem 1.10.

This is one layer below the effective-different-and-conductor component source:
the finite local different and conductor degrees are no longer arbitrary real
inputs.  They are the local degrees of the different and conductor arithmetic
divisors at the selected place.  Nonnegativity is therefore obtained from
effectivity of those divisors; the remaining source payload is the paper-side
identification of these divisor local degrees with the Proposition 1.4
tensor-different and tensor-conductor terms.
-/
structure IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDivisorBackedTensorDegreeComponentSource
    (place : Type u) [Fintype place]
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (arithmeticDivisorSource :
      IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate)
    (v0 : place)
    (α : Type v) (η : Type y) (K : Type w)
    [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (l : PrimeGeFive)
    (distinguishedProcessionBound arithmeticDegreeCoefficient : Real) where
  logShellSource :
    IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource
      α η K hullSystem l distinguishedProcessionBound
  formula_bound_eq_coarse_procession :
    distinguishedProcessionBound =
      logShellSource.coarseProcessionNormalizedUpperBound
  arithmeticDegreeCoefficient_ge_one :
    1 <= arithmeticDegreeCoefficient
  localDifferentDegree_eq_tensorDifferentPart :
    arithmeticDivisorSource.localDifferentDegree v0 =
      -logShellSource.lambda + logShellSource.dI +
        logShellSource.exceptionalRamificationLogSum
  localConductorDegree_eq_tensorConductorPart :
    arithmeticDivisorSource.localConductorDegree v0 =
      4 * Real.log (logShellSource.additiveHaarSource.residuePrime : Real)
  coarse_procession_le_tensorFormula :
    logShellSource.coarseProcessionNormalizedUpperBound <=
      iutIVProp14DistinguishedTensorBound
        logShellSource.additiveHaarSource.residuePrime
        logShellSource.lambda logShellSource.dI
        logShellSource.exceptionalRamificationLogSum

namespace IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDivisorBackedTensorDegreeComponentSource

set_option linter.style.longLine false

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {arithmeticDivisorSource :
  IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate}
variable {v0 : place}
variable {α : Type v} {η : Type y} {K : Type w}
variable [TopologicalSpace K] [MeasurableSpace K] [AddGroup K]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {l : PrimeGeFive}
variable {distinguishedProcessionBound arithmeticDegreeCoefficient : Real}

theorem localDifferentDegree_nonneg
    (_source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDivisorBackedTensorDegreeComponentSource
        place estimate arithmeticDivisorSource v0 α η K hullSystem l
        distinguishedProcessionBound arithmeticDegreeCoefficient) :
    0 <= arithmeticDivisorSource.localDifferentDegree v0 :=
  arithmeticDivisorSource.localDifferentDegree_nonneg v0

theorem localConductorDegree_nonneg
    (_source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDivisorBackedTensorDegreeComponentSource
        place estimate arithmeticDivisorSource v0 α η K hullSystem l
        distinguishedProcessionBound arithmeticDegreeCoefficient) :
    0 <= arithmeticDivisorSource.localConductorDegree v0 :=
  arithmeticDivisorSource.localConductorDegree_nonneg v0

set_option linter.style.longLine false in
noncomputable def toEffectiveDifferentConductorConstructedTensorDegreeComponentSource
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDivisorBackedTensorDegreeComponentSource
        place estimate arithmeticDivisorSource v0 α η K hullSystem l
        distinguishedProcessionBound arithmeticDegreeCoefficient) :
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarEffectiveDifferentConductorConstructedTensorDegreeComponentSource
      α η K hullSystem l distinguishedProcessionBound
      arithmeticDegreeCoefficient
      (arithmeticDivisorSource.localDifferentDegree v0)
      (arithmeticDivisorSource.localConductorDegree v0) :=
  { logShellSource := source.logShellSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    arithmeticLocalDifferentDegree_nonneg :=
      source.localDifferentDegree_nonneg,
    arithmeticLocalConductorDegree_nonneg :=
      source.localConductorDegree_nonneg,
    arithmeticLocalDifferentDegree_eq_tensorDifferentPart :=
      source.localDifferentDegree_eq_tensorDifferentPart,
    arithmeticLocalConductorDegree_eq_tensorConductorPart :=
      source.localConductorDegree_eq_tensorConductorPart,
    coarse_procession_le_tensorFormula :=
      source.coarse_procession_le_tensorFormula }

set_option linter.style.longLine false in
noncomputable def toConstructedTensorDegreeComponentSource
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDivisorBackedTensorDegreeComponentSource
        place estimate arithmeticDivisorSource v0 α η K hullSystem l
        distinguishedProcessionBound arithmeticDegreeCoefficient) :
    IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarConstructedTensorDegreeComponentSource
      α η K hullSystem l distinguishedProcessionBound
      arithmeticDegreeCoefficient :=
  source.toEffectiveDifferentConductorConstructedTensorDegreeComponentSource
    |>.toConstructedTensorDegreeComponentSource

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDivisorBackedTensorDegreeComponentSource
        place estimate arithmeticDivisorSource v0 α η K hullSystem l
        distinguishedProcessionBound arithmeticDegreeCoefficient) :
    Prop :=
  arithmeticDivisorSource.Endpoint ∧
    source.logShellSource.Endpoint ∧
      distinguishedProcessionBound =
        source.logShellSource.coarseProcessionNormalizedUpperBound ∧
        1 <= arithmeticDegreeCoefficient ∧
          0 <= arithmeticDivisorSource.localDifferentDegree v0 ∧
            0 <= arithmeticDivisorSource.localConductorDegree v0 ∧
              arithmeticDivisorSource.localDifferentDegree v0 =
                -source.logShellSource.lambda + source.logShellSource.dI +
                  source.logShellSource.exceptionalRamificationLogSum ∧
                arithmeticDivisorSource.localConductorDegree v0 =
                  4 * Real.log
                    (source.logShellSource.additiveHaarSource.residuePrime : Real) ∧
                  source.toEffectiveDifferentConductorConstructedTensorDegreeComponentSource.Endpoint ∧
                    source.toConstructedTensorDegreeComponentSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDivisorBackedTensorDegreeComponentSource
        place estimate arithmeticDivisorSource v0 α η K hullSystem l
        distinguishedProcessionBound arithmeticDegreeCoefficient) :
    Endpoint source :=
  ⟨arithmeticDivisorSource.endpoint,
    source.logShellSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.arithmeticDegreeCoefficient_ge_one,
    source.localDifferentDegree_nonneg,
    source.localConductorDegree_nonneg,
    source.localDifferentDegree_eq_tensorDifferentPart,
    source.localConductorDegree_eq_tensorConductorPart,
    source.toEffectiveDifferentConductorConstructedTensorDegreeComponentSource.endpoint,
    source.toConstructedTensorDegreeComponentSource.endpoint⟩

end IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarArithmeticDivisorBackedTensorDegreeComponentSource

set_option linter.style.longLine false in
/--
Archimedean unscaled local degree-bound source.

This records the Step (vii) coarse metric bound as an unscaled
different-plus-conductor degree bound before the arithmetic-degree coefficient
is applied.
-/
structure IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeBoundSource
    (I V : Type u) [Fintype I] [Fintype V]
    (l : PrimeGeFive)
    (archimedeanProcessionBound arithmeticDegreeCoefficient
      localDifferentDegree localConductorDegree : Real) where
  metricSource :
    IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
      I V l archimedeanProcessionBound
  formula_bound_eq_coarse_procession :
    archimedeanProcessionBound =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l
  arithmeticDegreeCoefficient_ge_one :
    1 <= arithmeticDegreeCoefficient
  localDifferentDegree_nonneg :
    0 <= localDifferentDegree
  localConductorDegree_nonneg :
    0 <= localConductorDegree
  archimedeanDegreeBound : Real
  archimedeanDegreeBound_eq_coarse :
    archimedeanDegreeBound =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l
  archimedeanDegreeBound_eq_different_conductor :
    archimedeanDegreeBound = localDifferentDegree + localConductorDegree

namespace IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeBoundSource

set_option linter.style.longLine false

variable {I V : Type u} [Fintype I] [Fintype V]
variable {l : PrimeGeFive}
variable {archimedeanProcessionBound arithmeticDegreeCoefficient
  localDifferentDegree localConductorDegree : Real}

theorem coarse_procession_le_different_conductor_degree
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeBoundSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    iutIVThetaPilotStepVIIArchimedeanCoarseBound l <=
      localDifferentDegree + localConductorDegree := by
  rw [← source.archimedeanDegreeBound_eq_different_conductor]
  exact le_of_eq source.archimedeanDegreeBound_eq_coarse.symm

def toDerivedArithmeticDegreeComparisonSource
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeBoundSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    IUTStage1IUTIVTheorem110ArchimedeanMetricDerivedArithmeticDegreeComparisonSource
      I V l archimedeanProcessionBound arithmeticDegreeCoefficient
      localDifferentDegree localConductorDegree :=
  { metricSource := source.metricSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    localDifferentDegree_nonneg :=
      source.localDifferentDegree_nonneg,
    localConductorDegree_nonneg :=
      source.localConductorDegree_nonneg,
    coarse_procession_le_different_conductor_degree :=
      source.coarse_procession_le_different_conductor_degree }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeBoundSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    Prop :=
  source.metricSource.Endpoint ∧
    archimedeanProcessionBound =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l ∧
      1 <= arithmeticDegreeCoefficient ∧
        0 <= localDifferentDegree ∧
          0 <= localConductorDegree ∧
            source.archimedeanDegreeBound =
              iutIVThetaPilotStepVIIArchimedeanCoarseBound l ∧
              source.archimedeanDegreeBound =
                localDifferentDegree + localConductorDegree ∧
                iutIVThetaPilotStepVIIArchimedeanCoarseBound l <=
                  localDifferentDegree + localConductorDegree ∧
                  source.toDerivedArithmeticDegreeComparisonSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeBoundSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    Endpoint source :=
  ⟨source.metricSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.arithmeticDegreeCoefficient_ge_one,
    source.localDifferentDegree_nonneg,
    source.localConductorDegree_nonneg,
    source.archimedeanDegreeBound_eq_coarse,
    source.archimedeanDegreeBound_eq_different_conductor,
    source.coarse_procession_le_different_conductor_degree,
    source.toDerivedArithmeticDegreeComparisonSource.endpoint⟩

end IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeBoundSource

set_option linter.style.longLine false in
/--
Archimedean local degree-identification source below the unscaled Theorem 1.10
arithmetic-degree comparison.

This is the Step (vii) analogue of the distinguished identification source:
the coarse archimedean bound is identified with the local
different-plus-conductor degree before the existing unscaled source derives the
comparison needed for the arithmetic-degree scaling step.
-/
structure IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeIdentificationSource
    (I V : Type u) [Fintype I] [Fintype V]
    (l : PrimeGeFive)
    (archimedeanProcessionBound arithmeticDegreeCoefficient
      localDifferentDegree localConductorDegree : Real) where
  metricSource :
    IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
      I V l archimedeanProcessionBound
  formula_bound_eq_coarse_procession :
    archimedeanProcessionBound =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l
  arithmeticDegreeCoefficient_ge_one :
    1 <= arithmeticDegreeCoefficient
  localDifferentDegree_nonneg :
    0 <= localDifferentDegree
  localConductorDegree_nonneg :
    0 <= localConductorDegree
  coarse_eq_different_conductor :
    iutIVThetaPilotStepVIIArchimedeanCoarseBound l =
      localDifferentDegree + localConductorDegree

namespace IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeIdentificationSource

set_option linter.style.longLine false

variable {I V : Type u} [Fintype I] [Fintype V]
variable {l : PrimeGeFive}
variable {archimedeanProcessionBound arithmeticDegreeCoefficient
  localDifferentDegree localConductorDegree : Real}

theorem coarse_procession_le_different_conductor_degree
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeIdentificationSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    iutIVThetaPilotStepVIIArchimedeanCoarseBound l <=
      localDifferentDegree + localConductorDegree :=
  le_of_eq source.coarse_eq_different_conductor

noncomputable def toUnscaledDegreeBoundSource
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeIdentificationSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeBoundSource
      I V l archimedeanProcessionBound arithmeticDegreeCoefficient
      localDifferentDegree localConductorDegree :=
  { metricSource := source.metricSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    localDifferentDegree_nonneg :=
      source.localDifferentDegree_nonneg,
    localConductorDegree_nonneg :=
      source.localConductorDegree_nonneg,
    archimedeanDegreeBound :=
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l,
    archimedeanDegreeBound_eq_coarse := rfl,
    archimedeanDegreeBound_eq_different_conductor :=
      source.coarse_eq_different_conductor }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeIdentificationSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    Prop :=
  source.metricSource.Endpoint ∧
    archimedeanProcessionBound =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l ∧
      1 <= arithmeticDegreeCoefficient ∧
        0 <= localDifferentDegree ∧
          0 <= localConductorDegree ∧
            iutIVThetaPilotStepVIIArchimedeanCoarseBound l =
              localDifferentDegree + localConductorDegree ∧
              iutIVThetaPilotStepVIIArchimedeanCoarseBound l <=
                localDifferentDegree + localConductorDegree ∧
                source.toUnscaledDegreeBoundSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeIdentificationSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    Endpoint source :=
  ⟨source.metricSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.arithmeticDegreeCoefficient_ge_one,
    source.localDifferentDegree_nonneg,
    source.localConductorDegree_nonneg,
    source.coarse_eq_different_conductor,
    source.coarse_procession_le_different_conductor_degree,
    source.toUnscaledDegreeBoundSource.endpoint⟩

end IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeIdentificationSource

set_option linter.style.longLine false in
/--
Archimedean metric component source for Theorem 1.10, Step (vii).

This lowers the archimedean degree-identification object by splitting the
coarse Step (vii) bound into the exact metric term
`((l+5)/4) log(pi)` and the nonnegative coarse-rounding remainder.  The old
degree-identification source is recovered by recombining these two components.
-/
structure IUTStage1IUTIVTheorem110ArchimedeanMetricDegreeComponentSource
    (I V : Type u) [Fintype I] [Fintype V]
    (l : PrimeGeFive)
    (archimedeanProcessionBound arithmeticDegreeCoefficient
      localDifferentDegree localConductorDegree : Real) where
  metricSource :
    IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
      I V l archimedeanProcessionBound
  formula_bound_eq_coarse_procession :
    archimedeanProcessionBound =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l
  arithmeticDegreeCoefficient_ge_one :
    1 <= arithmeticDegreeCoefficient
  localDifferentDegree_nonneg :
    0 <= localDifferentDegree
  localDifferentDegree_eq_exactMetricPart :
    localDifferentDegree =
      iutIVThetaPilotStepVIIArchimedeanExactBound l metricSource.logPi
  localConductorDegree_eq_coarseRemainder :
    localConductorDegree =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l -
        iutIVThetaPilotStepVIIArchimedeanExactBound l metricSource.logPi

namespace IUTStage1IUTIVTheorem110ArchimedeanMetricDegreeComponentSource

set_option linter.style.longLine false

variable {I V : Type u} [Fintype I] [Fintype V]
variable {l : PrimeGeFive}
variable {archimedeanProcessionBound arithmeticDegreeCoefficient
  localDifferentDegree localConductorDegree : Real}

theorem localConductorDegree_nonneg
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    0 <= localConductorDegree := by
  rw [source.localConductorDegree_eq_coarseRemainder]
  exact sub_nonneg.mpr
    (iutIVThetaPilotStepVIIArchimedeanExactBound_le_coarse
      l source.metricSource.logPi_le_two)

theorem coarse_eq_exactMetric_remainder
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    iutIVThetaPilotStepVIIArchimedeanCoarseBound l =
      localDifferentDegree + localConductorDegree := by
  calc
    iutIVThetaPilotStepVIIArchimedeanCoarseBound l =
        iutIVThetaPilotStepVIIArchimedeanExactBound l source.metricSource.logPi +
          (iutIVThetaPilotStepVIIArchimedeanCoarseBound l -
            iutIVThetaPilotStepVIIArchimedeanExactBound l source.metricSource.logPi) := by
      ring
    _ = localDifferentDegree + localConductorDegree := by
      rw [← source.localConductorDegree_eq_coarseRemainder,
        ← source.localDifferentDegree_eq_exactMetricPart]

set_option linter.style.longLine false in
noncomputable def toUnscaledDegreeIdentificationSource
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeIdentificationSource
      I V l archimedeanProcessionBound arithmeticDegreeCoefficient
      localDifferentDegree localConductorDegree :=
  { metricSource := source.metricSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    localDifferentDegree_nonneg :=
      source.localDifferentDegree_nonneg,
    localConductorDegree_nonneg :=
      source.localConductorDegree_nonneg,
    coarse_eq_different_conductor :=
      source.coarse_eq_exactMetric_remainder }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    Prop :=
  source.metricSource.Endpoint ∧
    archimedeanProcessionBound =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l ∧
      1 <= arithmeticDegreeCoefficient ∧
        0 <= localDifferentDegree ∧
          localDifferentDegree =
            iutIVThetaPilotStepVIIArchimedeanExactBound l
              source.metricSource.logPi ∧
            localConductorDegree =
              iutIVThetaPilotStepVIIArchimedeanCoarseBound l -
                iutIVThetaPilotStepVIIArchimedeanExactBound l
                  source.metricSource.logPi ∧
              0 <= localConductorDegree ∧
                iutIVThetaPilotStepVIIArchimedeanCoarseBound l =
                  localDifferentDegree + localConductorDegree ∧
                  source.toUnscaledDegreeIdentificationSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient
        localDifferentDegree localConductorDegree) :
    Endpoint source :=
  ⟨source.metricSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.arithmeticDegreeCoefficient_ge_one,
    source.localDifferentDegree_nonneg,
    source.localDifferentDegree_eq_exactMetricPart,
    source.localConductorDegree_eq_coarseRemainder,
    source.localConductorDegree_nonneg,
    source.coarse_eq_exactMetric_remainder,
    source.toUnscaledDegreeIdentificationSource.endpoint⟩

end IUTStage1IUTIVTheorem110ArchimedeanMetricDegreeComponentSource

set_option linter.style.longLine false in
/--
Constructed archimedean metric component source.

This is the source-facing form of the Step (vii) component split.  The local
different component is defined to be the exact metric contribution from the
Proposition 1.5 construction source, and the local conductor/coarse component is
defined to be the exact-to-coarse remainder.  Thus the component equalities of
`IUTStage1IUTIVTheorem110ArchimedeanMetricDegreeComponentSource` are no longer
supplied as arbitrary fields.
-/
structure IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource
    (I V : Type u) [Fintype I] [Fintype V]
    (l : PrimeGeFive)
    (archimedeanProcessionBound arithmeticDegreeCoefficient : Real) where
  metricSource :
    IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource
      I V l archimedeanProcessionBound
  formula_bound_eq_coarse_procession :
    archimedeanProcessionBound =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l
  arithmeticDegreeCoefficient_ge_one :
    1 <= arithmeticDegreeCoefficient
  exactMetricPart_nonneg :
    0 <= iutIVThetaPilotStepVIIArchimedeanExactBound l metricSource.logPi

namespace IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource

set_option linter.style.longLine false

variable {I V : Type u} [Fintype I] [Fintype V]
variable {l : PrimeGeFive}
variable {archimedeanProcessionBound arithmeticDegreeCoefficient : Real}

noncomputable def localDifferentDegree
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient) :
    Real :=
  iutIVThetaPilotStepVIIArchimedeanExactBound l source.metricSource.logPi

noncomputable def localConductorDegree
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient) :
    Real :=
  iutIVThetaPilotStepVIIArchimedeanCoarseBound l -
    iutIVThetaPilotStepVIIArchimedeanExactBound l source.metricSource.logPi

theorem localDifferentDegree_nonneg
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient) :
    0 <= source.localDifferentDegree := by
  simpa [localDifferentDegree] using source.exactMetricPart_nonneg

theorem localConductorDegree_nonneg
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient) :
    0 <= source.localConductorDegree := by
  dsimp [localConductorDegree]
  exact sub_nonneg.mpr
    (iutIVThetaPilotStepVIIArchimedeanExactBound_le_coarse
      l source.metricSource.logPi_le_two)

set_option linter.style.longLine false in
noncomputable def toDegreeComponentSource
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient) :
    IUTStage1IUTIVTheorem110ArchimedeanMetricDegreeComponentSource
      I V l archimedeanProcessionBound arithmeticDegreeCoefficient
      source.localDifferentDegree source.localConductorDegree :=
  { metricSource := source.metricSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    localDifferentDegree_nonneg :=
      source.localDifferentDegree_nonneg,
    localDifferentDegree_eq_exactMetricPart := by
      rfl,
    localConductorDegree_eq_coarseRemainder := by
      rfl }

set_option linter.style.longLine false in
noncomputable def toUnscaledDegreeIdentificationSource
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient) :
    IUTStage1IUTIVTheorem110ArchimedeanMetricUnscaledDegreeIdentificationSource
      I V l archimedeanProcessionBound arithmeticDegreeCoefficient
      source.localDifferentDegree source.localConductorDegree :=
  source.toDegreeComponentSource.toUnscaledDegreeIdentificationSource

set_option linter.style.longLine false in
noncomputable def toCalibratedDegreeComponentSource
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient)
    (localDifferentDegree localConductorDegree : Real)
    (localDifferentDegree_eq_constructed :
      localDifferentDegree = source.localDifferentDegree)
    (localConductorDegree_eq_constructed :
      localConductorDegree = source.localConductorDegree) :
    IUTStage1IUTIVTheorem110ArchimedeanMetricDegreeComponentSource
      I V l archimedeanProcessionBound arithmeticDegreeCoefficient
      localDifferentDegree localConductorDegree :=
  { metricSource := source.metricSource,
    formula_bound_eq_coarse_procession :=
      source.formula_bound_eq_coarse_procession,
    arithmeticDegreeCoefficient_ge_one :=
      source.arithmeticDegreeCoefficient_ge_one,
    localDifferentDegree_nonneg := by
      rw [localDifferentDegree_eq_constructed]
      exact source.localDifferentDegree_nonneg,
    localDifferentDegree_eq_exactMetricPart := by
      rw [localDifferentDegree_eq_constructed]
      rfl,
    localConductorDegree_eq_coarseRemainder := by
      rw [localConductorDegree_eq_constructed]
      rfl }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient) :
    Prop :=
  source.metricSource.Endpoint ∧
    archimedeanProcessionBound =
      iutIVThetaPilotStepVIIArchimedeanCoarseBound l ∧
      1 <= arithmeticDegreeCoefficient ∧
        0 <= source.localDifferentDegree ∧
          0 <= source.localConductorDegree ∧
            source.toDegreeComponentSource.Endpoint ∧
              source.toUnscaledDegreeIdentificationSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient) :
    Endpoint source :=
  ⟨source.metricSource.endpoint,
    source.formula_bound_eq_coarse_procession,
    source.arithmeticDegreeCoefficient_ge_one,
    source.localDifferentDegree_nonneg,
    source.localConductorDegree_nonneg,
    source.toDegreeComponentSource.endpoint,
    source.toUnscaledDegreeIdentificationSource.endpoint⟩

def CalibratedEndpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient)
    (localDifferentDegree localConductorDegree : Real)
    (localDifferentDegree_eq_constructed :
      localDifferentDegree = source.localDifferentDegree)
    (localConductorDegree_eq_constructed :
      localConductorDegree = source.localConductorDegree) :
    Prop :=
  source.Endpoint ∧
    0 <= localDifferentDegree ∧
      0 <= localConductorDegree ∧
        (source.toCalibratedDegreeComponentSource
          localDifferentDegree localConductorDegree
          localDifferentDegree_eq_constructed
          localConductorDegree_eq_constructed).Endpoint

theorem calibratedEndpoint
    (source :
      IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource
        I V l archimedeanProcessionBound arithmeticDegreeCoefficient)
    (localDifferentDegree localConductorDegree : Real)
    (localDifferentDegree_eq_constructed :
      localDifferentDegree = source.localDifferentDegree)
    (localConductorDegree_eq_constructed :
      localConductorDegree = source.localConductorDegree) :
    CalibratedEndpoint source localDifferentDegree localConductorDegree
      localDifferentDegree_eq_constructed
      localConductorDegree_eq_constructed := by
  refine ⟨source.endpoint, ?_, ?_, ?_⟩
  · rw [localDifferentDegree_eq_constructed]
    exact source.localDifferentDegree_nonneg
  · rw [localConductorDegree_eq_constructed]
    exact source.localConductorDegree_nonneg
  · exact
      (source.toCalibratedDegreeComponentSource
        localDifferentDegree localConductorDegree
        localDifferentDegree_eq_constructed
        localConductorDegree_eq_constructed).endpoint

end IUTStage1IUTIVTheorem110ArchimedeanMetricConstructedDegreeComponentSource

set_option linter.style.longLine false in
/--
Additive-Haar local analytic arithmetic-divisor source with named
formula-to-gap comparison objects.

This strengthens
`IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource`:
the distinguished and archimedean gap inequalities are no longer anonymous
families.  They are obtained from per-place comparison records that retain the
Proposition 1.4 additive-Haar log-shell source and Proposition 1.5 metric
source, respectively.
-/
structure IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
    (place : Type u) [Fintype place]
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (α : Type v) (η : Type w) (K : place -> Type x)
    [∀ placeId : place, TopologicalSpace (K placeId)]
    [∀ placeId : place, MeasurableSpace (K placeId)]
    [∀ placeId : place, AddGroup (K placeId)]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (archIndex archSummand : place -> Type v)
    [∀ placeId : place, Fintype (archIndex placeId)]
    [∀ placeId : place, Fintype (archSummand placeId)] where
  arithmeticDivisorSource :
    IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate
  additiveHaarLocalAnalyticConstructionFormulaSource :
    IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticConstructionFormulaSource
      place arithmeticDivisorSource α η K hullSystem archIndex archSummand
  distinguishedGapComparison :
    ∀ placeId : place,
      (hkind :
        additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarFormulaGapComparisonSource
          α η (K placeId) hullSystem estimate.l
          (additiveHaarLocalAnalyticConstructionFormulaSource.distinguishedProcessionBound
            placeId)
          (arithmeticDivisorSource.localArithmeticUpperContribution
              additiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            additiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId)
  distinguishedGapComparison_eq_construction :
    ∀ placeId : place,
      (hkind :
        additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        (distinguishedGapComparison placeId hkind).logShellSource =
          (additiveHaarLocalAnalyticConstructionFormulaSource).distinguishedAdditiveHaarLogShellConstruction
            placeId hkind
  archimedeanGapComparison :
    ∀ placeId : place,
      (hkind :
        additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        IUTStage1IUTIVTheorem110ArchimedeanMetricFormulaGapComparisonSource
          (archIndex placeId) (archSummand placeId) estimate.l
          (additiveHaarLocalAnalyticConstructionFormulaSource.archimedeanProcessionBound
            placeId)
          (arithmeticDivisorSource.localArithmeticUpperContribution
              additiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            additiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId)
  archimedeanGapComparison_eq_construction :
    ∀ placeId : place,
      (hkind :
        additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        (archimedeanGapComparison placeId hkind).metricSource =
          (additiveHaarLocalAnalyticConstructionFormulaSource).archimedeanMetricConstruction
            placeId hkind

namespace IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource

set_option linter.style.longLine false

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {α : Type v} {η : Type w} {K : place -> Type x}
variable [∀ placeId : place, TopologicalSpace (K placeId)]
variable [∀ placeId : place, MeasurableSpace (K placeId)]
variable [∀ placeId : place, AddGroup (K placeId)]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {archIndex archSummand : place -> Type v}
variable [∀ placeId : place, Fintype (archIndex placeId)]
variable [∀ placeId : place, Fintype (archSummand placeId)]

theorem distinguished_formula_le_gap
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand)
    (placeId : place)
    (hkind :
      source.additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
        IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) :
    source.additiveHaarLocalAnalyticConstructionFormulaSource.distinguishedProcessionBound
        placeId <=
      source.arithmeticDivisorSource.localArithmeticUpperContribution
          source.additiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
            placeId -
        source.additiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
          placeId :=
  (source.distinguishedGapComparison placeId hkind).formula_bound_le_gap

theorem archimedean_formula_le_gap
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand)
    (placeId : place)
    (hkind :
      source.additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
        IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) :
    source.additiveHaarLocalAnalyticConstructionFormulaSource.archimedeanProcessionBound
        placeId <=
      source.arithmeticDivisorSource.localArithmeticUpperContribution
          source.additiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
            placeId -
          source.additiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
          placeId :=
  (source.archimedeanGapComparison placeId hkind).formula_bound_le_gap

noncomputable def ofAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
      place estimate α η K hullSystem archIndex archSummand :=
  { arithmeticDivisorSource := source.arithmeticDivisorSource,
    additiveHaarLocalAnalyticConstructionFormulaSource :=
      source.additiveHaarLocalAnalyticConstructionFormulaSource,
    distinguishedGapComparison := fun placeId hkind =>
      { logShellSource :=
          source.additiveHaarLocalAnalyticConstructionFormulaSource
            |>.distinguishedAdditiveHaarLogShellConstruction placeId hkind,
        formula_bound_le_gap :=
          source.distinguished_formula_le_gap placeId hkind },
    distinguishedGapComparison_eq_construction := fun _ _ => rfl,
    archimedeanGapComparison := fun placeId hkind =>
      { metricSource :=
          source.additiveHaarLocalAnalyticConstructionFormulaSource
            |>.archimedeanMetricConstruction placeId hkind,
        formula_bound_le_gap :=
          source.archimedean_formula_le_gap placeId hkind },
    archimedeanGapComparison_eq_construction := fun _ _ => rfl }

noncomputable def toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
      place estimate α η K hullSystem archIndex archSummand :=
  { arithmeticDivisorSource := source.arithmeticDivisorSource,
    additiveHaarLocalAnalyticConstructionFormulaSource :=
      source.additiveHaarLocalAnalyticConstructionFormulaSource,
    distinguished_formula_le_gap :=
      source.distinguished_formula_le_gap,
    archimedean_formula_le_gap :=
      source.archimedean_formula_le_gap }

def Endpoint
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    Prop :=
  source.additiveHaarLocalAnalyticConstructionFormulaSource.Endpoint ∧
    (∀ placeId : place,
      (hkind :
        source.additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        (source.distinguishedGapComparison placeId hkind).Endpoint ∧
          (source.distinguishedGapComparison placeId hkind).logShellSource =
            (source.additiveHaarLocalAnalyticConstructionFormulaSource).distinguishedAdditiveHaarLogShellConstruction
              placeId hkind) ∧
      (∀ placeId : place,
        (hkind :
          source.additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
            IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
          (source.archimedeanGapComparison placeId hkind).Endpoint ∧
            (source.archimedeanGapComparison placeId hkind).metricSource =
              (source.additiveHaarLocalAnalyticConstructionFormulaSource).archimedeanMetricConstruction
                placeId hkind) ∧
        source.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.Endpoint

theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    Endpoint source :=
  ⟨source.additiveHaarLocalAnalyticConstructionFormulaSource.endpoint,
    (fun placeId hkind =>
      ⟨(source.distinguishedGapComparison placeId hkind).endpoint,
        source.distinguishedGapComparison_eq_construction placeId hkind⟩),
    (fun placeId hkind =>
      ⟨(source.archimedeanGapComparison placeId hkind).endpoint,
        source.archimedeanGapComparison_eq_construction placeId hkind⟩),
    source.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.endpoint⟩

set_option linter.style.longLine false in
/--
Local formula-gap audit for the IUT IV Theorem 1.10 arithmetic-divisor
evaluation source.

This is the paper-facing Step (v)/Step (vii) checkpoint: distinguished
Proposition 1.4 log-shell containers and archimedean Proposition 1.5 metric
containers are not merely present as construction sources; their container
bounds are proved below the local arithmetic-upper-minus-main-log gaps used by
the Theorem 1.10 summation.
-/
structure FormulaGapLocalEstimateAudit
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) : Prop where
  endpoint : Endpoint source
  distinguishedGapComparisonEndpoint :
    ∀ placeId,
      (hkind :
        source.additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        (source.distinguishedGapComparison placeId hkind).Endpoint
  distinguishedLogShell_eq_construction :
    ∀ placeId,
      (hkind :
        source.additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        (source.distinguishedGapComparison placeId hkind).logShellSource =
          source.additiveHaarLocalAnalyticConstructionFormulaSource.distinguishedAdditiveHaarLogShellConstruction
            placeId hkind
  distinguishedFormulaBound_le_gap :
    ∀ placeId,
      (hkind :
        source.additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        source.additiveHaarLocalAnalyticConstructionFormulaSource.distinguishedProcessionBound
            placeId <=
          source.arithmeticDivisorSource.localArithmeticUpperContribution
              source.additiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            source.additiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId
  distinguishedProp14Container_le_gap :
    ∀ placeId,
      (hkind :
        source.additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        ((source.distinguishedGapComparison placeId hkind).logShellSource.toDistinguishedLocalLogShellConstructionSource.toDistinguishedLocalLogShellEstimate).prop14ContainerUpperBound <=
          source.arithmeticDivisorSource.localArithmeticUpperContribution
              source.additiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            source.additiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId
  archimedeanGapComparisonEndpoint :
    ∀ placeId,
      (hkind :
        source.additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        (source.archimedeanGapComparison placeId hkind).Endpoint
  archimedeanMetric_eq_construction :
    ∀ placeId,
      (hkind :
        source.additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        (source.archimedeanGapComparison placeId hkind).metricSource =
          source.additiveHaarLocalAnalyticConstructionFormulaSource.archimedeanMetricConstruction
            placeId hkind
  archimedeanFormulaBound_le_gap :
    ∀ placeId,
      (hkind :
        source.additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        source.additiveHaarLocalAnalyticConstructionFormulaSource.archimedeanProcessionBound
            placeId <=
          source.arithmeticDivisorSource.localArithmeticUpperContribution
              source.additiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            source.additiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId
  archimedeanMetricContainer_le_gap :
    ∀ placeId,
      (hkind :
        source.additiveHaarLocalAnalyticConstructionFormulaSource.localKind placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        (source.archimedeanGapComparison placeId hkind).metricSource.metricContainerLogVolume <=
          source.arithmeticDivisorSource.localArithmeticUpperContribution
              source.additiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            source.additiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId
  projectedLocalAnalyticEndpoint :
    source.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.Endpoint

set_option linter.style.longLine false in
theorem formulaGapLocalEstimateAudit
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    FormulaGapLocalEstimateAudit source :=
  { endpoint := source.endpoint,
    distinguishedGapComparisonEndpoint := fun placeId hkind =>
      (source.distinguishedGapComparison placeId hkind).endpoint,
    distinguishedLogShell_eq_construction := fun placeId hkind =>
      source.distinguishedGapComparison_eq_construction placeId hkind,
    distinguishedFormulaBound_le_gap := source.distinguished_formula_le_gap,
    distinguishedProp14Container_le_gap := fun placeId hkind =>
      (source.distinguishedGapComparison placeId hkind).prop14Container_le_gap,
    archimedeanGapComparisonEndpoint := fun placeId hkind =>
      (source.archimedeanGapComparison placeId hkind).endpoint,
    archimedeanMetric_eq_construction := fun placeId hkind =>
      source.archimedeanGapComparison_eq_construction placeId hkind,
    archimedeanFormulaBound_le_gap := source.archimedean_formula_le_gap,
    archimedeanMetricContainer_le_gap := fun placeId hkind =>
      (source.archimedeanGapComparison placeId hkind).metricContainer_le_gap,
    projectedLocalAnalyticEndpoint :=
      source.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.endpoint }

theorem ofAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource_endpoint
    (source :
      IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    Endpoint
      (ofAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource source) :=
  (ofAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource source).endpoint

end IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource

set_option linter.style.longLine false in
/--
Valuation-ball additive-Haar local analytic arithmetic-divisor source with
named formula-to-gap comparison objects.

This is the valuation-ball refinement of
`IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource`.
The finite Proposition 1.4 constructions are valuation-ball Haar sources; the
named Step (v)/Step (vii) formula-to-gap comparisons are then projected to the
additive-Haar formula-gap matched route.
-/
structure IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
    (place : Type u) [Fintype place]
    (estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow)
    (α : Type v) (η : Type w) (K : place -> Type x)
    [∀ placeId : place, TopologicalSpace (K placeId)]
    [∀ placeId : place, MeasurableSpace (K placeId)]
    [∀ placeId : place, AddGroup (K placeId)]
    [∀ placeId : place, T2Space (K placeId)]
    (hullSystem : IUTStage1Remark395HolomorphicHullSystem α)
    (archIndex archSummand : place -> Type v)
    [∀ placeId : place, Fintype (archIndex placeId)]
    [∀ placeId : place, Fintype (archSummand placeId)] where
  arithmeticDivisorSource :
    IUTStage1IUTIVTheorem110ArithmeticDivisorSource place estimate
  valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource :
    IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
      place arithmeticDivisorSource α η K hullSystem archIndex archSummand
  distinguishedGapComparison :
    ∀ placeId : place,
      (hkind :
        valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
            placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        IUTStage1IUTIVTheorem110DistinguishedAdditiveHaarFormulaGapComparisonSource
          α η (K placeId) hullSystem estimate.l
          (valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.distinguishedProcessionBound
            placeId)
          (arithmeticDivisorSource.localArithmeticUpperContribution
              valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId)
  distinguishedGapComparison_eq_construction :
    ∀ placeId : place,
      (hkind :
        valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
            placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        (distinguishedGapComparison placeId hkind).logShellSource =
          ((valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource).distinguishedValuationBallAdditiveHaarLogShellConstruction
            placeId hkind).toAdditiveHaarLogShellSource
  archimedeanGapComparison :
    ∀ placeId : place,
      (hkind :
        valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
            placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        IUTStage1IUTIVTheorem110ArchimedeanMetricFormulaGapComparisonSource
          (archIndex placeId) (archSummand placeId) estimate.l
          (valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.archimedeanProcessionBound
            placeId)
          (arithmeticDivisorSource.localArithmeticUpperContribution
              valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId)
  archimedeanGapComparison_eq_construction :
    ∀ placeId : place,
      (hkind :
        valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
            placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        (archimedeanGapComparison placeId hkind).metricSource =
          (valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource).archimedeanMetricConstruction
            placeId hkind

set_option linter.style.longLine false
namespace IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource

variable {place : Type u} [Fintype place]
variable {estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow}
variable {α : Type v} {η : Type w} {K : place -> Type x}
variable [∀ placeId : place, TopologicalSpace (K placeId)]
variable [∀ placeId : place, MeasurableSpace (K placeId)]
variable [∀ placeId : place, AddGroup (K placeId)]
variable [∀ placeId : place, T2Space (K placeId)]
variable {hullSystem : IUTStage1Remark395HolomorphicHullSystem α}
variable {archIndex archSummand : place -> Type v}
variable [∀ placeId : place, Fintype (archIndex placeId)]
variable [∀ placeId : place, Fintype (archSummand placeId)]

theorem distinguished_formula_le_gap
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand)
    (placeId : place)
    (hkind :
      source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
          placeId =
        IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) :
    source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.distinguishedProcessionBound
        placeId <=
      source.arithmeticDivisorSource.localArithmeticUpperContribution
          source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
            placeId -
        source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
          placeId :=
  (source.distinguishedGapComparison placeId hkind).formula_bound_le_gap

theorem archimedean_formula_le_gap
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand)
    (placeId : place)
    (hkind :
      source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
          placeId =
        IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) :
    source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.archimedeanProcessionBound
        placeId <=
      source.arithmeticDivisorSource.localArithmeticUpperContribution
          source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
            placeId -
        source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
          placeId :=
  (source.archimedeanGapComparison placeId hkind).formula_bound_le_gap

set_option linter.style.longLine false in
noncomputable def toAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
      place estimate α η K hullSystem archIndex archSummand :=
  { arithmeticDivisorSource := source.arithmeticDivisorSource,
    additiveHaarLocalAnalyticConstructionFormulaSource :=
      source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
        |>.toAdditiveHaarLocalAnalyticConstructionFormulaSource,
    distinguishedGapComparison := by
      intro placeId hkind
      exact source.distinguishedGapComparison placeId (by
        simpa [
          IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.toAdditiveHaarLocalAnalyticConstructionFormulaSource] using
          hkind),
    distinguishedGapComparison_eq_construction := by
      intro placeId hkind
      simpa [
        IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.toAdditiveHaarLocalAnalyticConstructionFormulaSource] using
        source.distinguishedGapComparison_eq_construction placeId (by
          simpa [
            IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.toAdditiveHaarLocalAnalyticConstructionFormulaSource] using
            hkind),
    archimedeanGapComparison := by
      intro placeId hkind
      exact source.archimedeanGapComparison placeId (by
        simpa [
          IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.toAdditiveHaarLocalAnalyticConstructionFormulaSource] using
          hkind),
    archimedeanGapComparison_eq_construction := by
      intro placeId hkind
      simpa [
        IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.toAdditiveHaarLocalAnalyticConstructionFormulaSource] using
        source.archimedeanGapComparison_eq_construction placeId (by
          simpa [
            IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.toAdditiveHaarLocalAnalyticConstructionFormulaSource] using
            hkind) }

set_option linter.style.longLine false in
noncomputable def ofValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
      place estimate α η K hullSystem archIndex archSummand :=
  { arithmeticDivisorSource := source.arithmeticDivisorSource,
    valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource :=
      source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource,
    distinguishedGapComparison := fun placeId hkind =>
      { logShellSource :=
          (source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
            |>.distinguishedValuationBallAdditiveHaarLogShellConstruction
              placeId hkind).toAdditiveHaarLogShellSource,
        formula_bound_le_gap :=
          source.distinguished_formula_le_gap placeId hkind },
    distinguishedGapComparison_eq_construction := fun _ _ => rfl,
    archimedeanGapComparison := fun placeId hkind =>
      { metricSource :=
          source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
            |>.archimedeanMetricConstruction placeId hkind,
        formula_bound_le_gap :=
          source.archimedean_formula_le_gap placeId hkind },
    archimedeanGapComparison_eq_construction := fun _ _ => rfl }

set_option linter.style.longLine false in
noncomputable def toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
      place estimate α η K hullSystem archIndex archSummand :=
  { arithmeticDivisorSource := source.arithmeticDivisorSource,
    valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource :=
      source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource,
    distinguished_formula_le_gap :=
      source.distinguished_formula_le_gap,
    archimedean_formula_le_gap :=
      source.archimedean_formula_le_gap }

set_option linter.style.longLine false in
noncomputable def toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110AdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
      place estimate α η K hullSystem archIndex archSummand :=
  source.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    |>.toAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource

set_option linter.style.longLine false in
noncomputable def toFormulaArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    IUTStage1IUTIVTheorem110FormulaArithmeticDivisorEvaluationSource
      place estimate :=
  source.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    |>.toFormulaArithmeticDivisorEvaluationSource

set_option linter.style.longLine false in
def Endpoint
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    Prop :=
  source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.Endpoint ∧
    (∀ placeId : place,
      (hkind :
        source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
            placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
          (source.distinguishedGapComparison placeId hkind).Endpoint ∧
            (source.distinguishedGapComparison placeId hkind).logShellSource =
            ((source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource).distinguishedValuationBallAdditiveHaarLogShellConstruction
              placeId hkind).toAdditiveHaarLogShellSource) ∧
      (∀ placeId : place,
        (hkind :
          source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
              placeId =
            IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
          (source.archimedeanGapComparison placeId hkind).Endpoint ∧
            (source.archimedeanGapComparison placeId hkind).metricSource =
              (source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource).archimedeanMetricConstruction
                placeId hkind) ∧
        source.toAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource.Endpoint ∧
          source.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.Endpoint

set_option linter.style.longLine false in
theorem endpoint
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    Endpoint source :=
  ⟨source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.endpoint,
    (fun placeId hkind =>
      ⟨(source.distinguishedGapComparison placeId hkind).endpoint,
        source.distinguishedGapComparison_eq_construction placeId hkind⟩),
    (fun placeId hkind =>
      ⟨(source.archimedeanGapComparison placeId hkind).endpoint,
        source.archimedeanGapComparison_eq_construction placeId hkind⟩),
    source.toAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource.endpoint,
    source.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.endpoint⟩

set_option linter.style.longLine false in
theorem ofValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource_endpoint
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    Endpoint
      (ofValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource source) :=
  (ofValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource source).endpoint

set_option linter.style.longLine false in
theorem toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource_ofValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    (ofValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource source
      |>.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource) =
        source := by
  rfl

set_option linter.style.longLine false in
/--
Valuation-ball formula-gap audit for the IUT IV Theorem 1.10 local estimate.

This is the valuation-ball refinement of
`FormulaGapLocalEstimateAudit`: the distinguished finite-place comparison is
not merely an additive-Haar log-shell comparison.  It is witnessed by the
valuation-ball Proposition 1.4 source, then projected to the additive-Haar
formula-gap comparison used by the global summation.
-/
structure ValuationBallFormulaGapLocalEstimateAudit
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) : Prop where
  endpoint : Endpoint source
  additiveFormulaGapAudit :
    IUTStage1IUTIVTheorem110AdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource.FormulaGapLocalEstimateAudit
      source.toAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
  valuationBallSourceIngredientAudit :
    IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource.SourceIngredientAudit
      source.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
  distinguishedValuationBallLogShellEndpoint :
    ∀ placeId,
      (hkind :
        source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
            placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        (source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
          |>.distinguishedValuationBallAdditiveHaarLogShellConstruction
            placeId hkind).Endpoint
  distinguishedAdditiveLogShell_eq_valuationBallProjection :
    ∀ placeId,
      (hkind :
        source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
            placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        (source.distinguishedGapComparison placeId hkind).logShellSource =
          ((source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource)
            |>.distinguishedValuationBallAdditiveHaarLogShellConstruction
              placeId hkind).toAdditiveHaarLogShellSource
  distinguishedValuationBallContainer_le_gap :
    ∀ placeId,
      (hkind :
        source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
            placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.distinguishedNonarchimedean) ->
        (((source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
          |>.distinguishedValuationBallAdditiveHaarLogShellConstruction
            placeId hkind).toDistinguishedLocalLogShellConstructionSource)
              |>.toDistinguishedLocalLogShellEstimate).prop14ContainerUpperBound <=
          source.arithmeticDivisorSource.localArithmeticUpperContribution
              source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId
  archimedeanMetricEndpoint :
    ∀ placeId,
      (hkind :
        source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
            placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        (source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
          |>.archimedeanMetricConstruction placeId hkind).Endpoint
  archimedeanMetric_eq_construction :
    ∀ placeId,
      (hkind :
        source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
            placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        (source.archimedeanGapComparison placeId hkind).metricSource =
          (source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
            |>.archimedeanMetricConstruction placeId hkind)
  archimedeanMetricContainer_le_gap :
    ∀ placeId,
      (hkind :
        source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localKind
            placeId =
          IUTStage1IUTIVTheorem110LocalEstimateKind.archimedean) ->
        (source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
          |>.archimedeanMetricConstruction placeId hkind).metricContainerLogVolume <=
          source.arithmeticDivisorSource.localArithmeticUpperContribution
              source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localPrimeErrorContribution
                placeId -
            source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource.localMainLogContribution
              placeId

set_option linter.style.longLine false in
theorem valuationBallFormulaGapLocalEstimateAudit
    (source :
      IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        place estimate α η K hullSystem archIndex archSummand) :
    ValuationBallFormulaGapLocalEstimateAudit source :=
  { endpoint := source.endpoint,
    additiveFormulaGapAudit :=
      source.toAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
        |>.formulaGapLocalEstimateAudit,
    valuationBallSourceIngredientAudit :=
      source.toValuationBallAdditiveHaarLocalAnalyticArithmeticDivisorEvaluationSource
        |>.sourceIngredientAudit,
    distinguishedValuationBallLogShellEndpoint := by
      intro placeId hkind
      exact
        (source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
          |>.distinguishedValuationBallAdditiveHaarLogShellConstruction
            placeId hkind).endpoint,
    distinguishedAdditiveLogShell_eq_valuationBallProjection := by
      intro placeId hkind
      exact source.distinguishedGapComparison_eq_construction placeId hkind,
    distinguishedValuationBallContainer_le_gap := by
      intro placeId hkind
      simpa [
        source.distinguishedGapComparison_eq_construction placeId hkind
      ] using
        (source.distinguishedGapComparison placeId hkind).prop14Container_le_gap,
    archimedeanMetricEndpoint := by
      intro placeId hkind
      exact
        (source.valuationBallAdditiveHaarLocalAnalyticConstructionFormulaSource
          |>.archimedeanMetricConstruction placeId hkind).endpoint,
    archimedeanMetric_eq_construction := by
      intro placeId hkind
      exact source.archimedeanGapComparison_eq_construction placeId hkind,
    archimedeanMetricContainer_le_gap := by
      intro placeId hkind
      simpa [
        source.archimedeanGapComparison_eq_construction placeId hkind
      ] using
        (source.archimedeanGapComparison placeId hkind).metricContainer_le_gap }

end IUTStage1IUTIVTheorem110ValuationBallAdditiveHaarFormulaGapMatchedArithmeticDivisorEvaluationSource
set_option linter.style.longLine true

/--
IUT IV, Theorem 1.10 final displayed bound after the tripodal-to-`F` passage.

This record composes two already-formalized pieces of the theorem: the
Corollary 3.12 handoff giving the `F_tpd` right-hand side, and the monotonicity
`log(d_Ftpd) <= log(d_F)`, `log(f_Ftpd) <= log(f_F)` that yields the final
right-hand side in the statement of Theorem 1.10.
-/
structure IUTStage1IUTIVTheorem110FinalDisplayShadow where
  estimate : IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow
  logDifferentF : Real
  logConductorF : Real
  different_le : estimate.logDifferentFtpd <= logDifferentF
  conductor_le : estimate.logConductorFtpd <= logConductorF

namespace IUTStage1IUTIVTheorem110FinalDisplayShadow

noncomputable def finalRightHandSide
    (data : IUTStage1IUTIVTheorem110FinalDisplayShadow) : Real :=
  iutIVThetaPilotTheorem110RightHandSide data.estimate.l data.estimate.dmod
    data.logDifferentF data.logConductorF data.estimate.eStarMod
    data.estimate.etaPrm

def baseChange
    (data : IUTStage1IUTIVTheorem110FinalDisplayShadow) :
    IUTStage1IUTIVTripodalBaseChangeLogDegreeShadow :=
  { l := data.estimate.l
    dmod := data.estimate.dmod
    logDifferentFtpd := data.estimate.logDifferentFtpd
    logConductorFtpd := data.estimate.logConductorFtpd
    logDifferentF := data.logDifferentF
    logConductorF := data.logConductorF
    eStarMod := data.estimate.eStarMod
    etaPrm := data.estimate.etaPrm
    different_le := data.different_le
    conductor_le := data.conductor_le }

theorem finalRightHandSide_eq_baseChange
    (data : IUTStage1IUTIVTheorem110FinalDisplayShadow) :
    data.finalRightHandSide = data.baseChange.fTheorem110RightHandSide :=
  rfl

theorem oneSixthLogQ_le_ftpdRightHandSide
    (data : IUTStage1IUTIVTheorem110FinalDisplayShadow) :
    data.estimate.oneSixthLogQ <= data.baseChange.ftpdTheorem110RightHandSide :=
  data.estimate.oneSixthLogQ_le_theorem110RightHandSide

theorem ftpdRightHandSide_le_finalRightHandSide
    (data : IUTStage1IUTIVTheorem110FinalDisplayShadow) :
    data.baseChange.ftpdTheorem110RightHandSide <= data.finalRightHandSide :=
  data.baseChange.ftpdTheorem110RightHandSide_le_fTheorem110RightHandSide

theorem oneSixthLogQ_le_finalRightHandSide
    (data : IUTStage1IUTIVTheorem110FinalDisplayShadow) :
    data.estimate.oneSixthLogQ <= data.finalRightHandSide := by
  exact le_trans data.oneSixthLogQ_le_ftpdRightHandSide
    data.ftpdRightHandSide_le_finalRightHandSide

theorem final_display_chain
    (data : IUTStage1IUTIVTheorem110FinalDisplayShadow) :
    data.estimate.oneSixthLogQ <= data.baseChange.ftpdTheorem110RightHandSide ∧
      data.baseChange.ftpdTheorem110RightHandSide <= data.finalRightHandSide ∧
        data.estimate.oneSixthLogQ <= data.finalRightHandSide :=
  ⟨data.oneSixthLogQ_le_ftpdRightHandSide,
    data.ftpdRightHandSide_le_finalRightHandSide,
    data.oneSixthLogQ_le_finalRightHandSide⟩

end IUTStage1IUTIVTheorem110FinalDisplayShadow

/--
IUT IV, Theorem A bounded-discrepancy inequality.

Theorem A states, for a hyperbolic curve `U_X = X \ D` and points of extension
degree at most `d`, that
`(1 + epsilon) * (logDiff + logCond) - height` is bounded below.  This record
does not construct the height, different, or conductor functions; it records the
exact real-valued bounded-discrepancy conclusion that Theorem A asserts.
-/
structure IUTStage1IUTIVTheoremABoundedDiscrepancyShadow
    (Point : Type u) where
  d : Nat
  d_pos : 0 < d
  epsilon : Real
  epsilon_pos : 0 < epsilon
  hyperbolicCurve : Prop
  hyperbolic_curve : hyperbolicCurve
  height : Point -> Real
  logDiff : Point -> Real
  logCond : Point -> Real
  lowerBound : Real
  discrepancy_bounded_below :
    ∀ x : Point,
      lowerBound <=
        (1 + epsilon) * (logDiff x + logCond x) - height x

namespace IUTStage1IUTIVTheoremABoundedDiscrepancyShadow

variable {Point : Type u}

def discrepancy
    (data : IUTStage1IUTIVTheoremABoundedDiscrepancyShadow Point)
    (x : Point) : Real :=
  (1 + data.epsilon) * (data.logDiff x + data.logCond x) - data.height x

theorem discrepancy_lower_bound
    (data : IUTStage1IUTIVTheoremABoundedDiscrepancyShadow Point)
    (x : Point) :
    data.lowerBound <= data.discrepancy x :=
  data.discrepancy_bounded_below x

theorem one_plus_epsilon_pos
    (data : IUTStage1IUTIVTheoremABoundedDiscrepancyShadow Point) :
    0 < 1 + data.epsilon := by
  linarith [data.epsilon_pos]

theorem height_add_lowerBound_le_weighted_logDiff_logCond
    (data : IUTStage1IUTIVTheoremABoundedDiscrepancyShadow Point)
    (x : Point) :
    data.height x + data.lowerBound <=
      (1 + data.epsilon) * (data.logDiff x + data.logCond x) := by
  have h := data.discrepancy_lower_bound x
  dsimp [discrepancy] at h
  linarith

theorem height_le_weighted_logDiff_logCond_minus_lowerBound
    (data : IUTStage1IUTIVTheoremABoundedDiscrepancyShadow Point)
    (x : Point) :
    data.height x <=
      (1 + data.epsilon) * (data.logDiff x + data.logCond x) -
        data.lowerBound := by
  have h := data.height_add_lowerBound_le_weighted_logDiff_logCond x
  linarith

theorem hyperbolicCurve_holds
    (data : IUTStage1IUTIVTheoremABoundedDiscrepancyShadow Point) :
    data.hyperbolicCurve :=
  data.hyperbolic_curve

theorem theoremA_bounded_discrepancy_endpoint
    (data : IUTStage1IUTIVTheoremABoundedDiscrepancyShadow Point)
    (x : Point) :
    data.hyperbolicCurve ∧
      0 < 1 + data.epsilon ∧
      data.lowerBound <= data.discrepancy x ∧
      data.height x + data.lowerBound <=
        (1 + data.epsilon) * (data.logDiff x + data.logCond x) ∧
      data.height x <=
        (1 + data.epsilon) * (data.logDiff x + data.logCond x) -
          data.lowerBound :=
  ⟨data.hyperbolicCurve_holds,
    data.one_plus_epsilon_pos,
    data.discrepancy_lower_bound x,
    data.height_add_lowerBound_le_weighted_logDiff_logCond x,
    data.height_le_weighted_logDiff_logCond_minus_lowerBound x⟩

end IUTStage1IUTIVTheoremABoundedDiscrepancyShadow

/--
Real-valued equality up to bounded discrepancy.

This is the function-level relation used in IUT IV and GenEll when writing
`f ≈ g`: the difference `f - g` is bounded above and below by constants on the
specified point set.
-/
structure IUTStage1BoundedDiscrepancyEquivalent
    (Point : Type u) (f g : Point -> Real) where
  lower : Real
  upper : Real
  lower_bound : ∀ x : Point, lower <= f x - g x
  upper_bound : ∀ x : Point, f x - g x <= upper

namespace IUTStage1BoundedDiscrepancyEquivalent

variable {Point : Type u} {f g h : Point -> Real}

def refl (f : Point -> Real) :
    IUTStage1BoundedDiscrepancyEquivalent Point f f :=
  { lower := 0
    upper := 0
    lower_bound := by intro x; simp
    upper_bound := by intro x; simp }

def symm
    (data : IUTStage1BoundedDiscrepancyEquivalent Point f g) :
    IUTStage1BoundedDiscrepancyEquivalent Point g f :=
  { lower := -data.upper
    upper := -data.lower
    lower_bound := by
      intro x
      have hupper := data.upper_bound x
      linarith
    upper_bound := by
      intro x
      have hlower := data.lower_bound x
      linarith }

def trans
    (fg : IUTStage1BoundedDiscrepancyEquivalent Point f g)
    (gh : IUTStage1BoundedDiscrepancyEquivalent Point g h) :
    IUTStage1BoundedDiscrepancyEquivalent Point f h :=
  { lower := fg.lower + gh.lower
    upper := fg.upper + gh.upper
    lower_bound := by
      intro x
      have hfg := fg.lower_bound x
      have hgh := gh.lower_bound x
      linarith
    upper_bound := by
      intro x
      have hfg := fg.upper_bound x
      have hgh := gh.upper_bound x
      linarith }

def scale
    (c : Real) (hc : 0 <= c)
    (data : IUTStage1BoundedDiscrepancyEquivalent Point f g) :
    IUTStage1BoundedDiscrepancyEquivalent Point
      (fun x => c * f x) (fun x => c * g x) :=
  { lower := c * data.lower
    upper := c * data.upper
    lower_bound := by
      intro x
      have h := mul_le_mul_of_nonneg_left (data.lower_bound x) hc
      linarith
    upper_bound := by
      intro x
      have h := mul_le_mul_of_nonneg_left (data.upper_bound x) hc
      linarith }

theorem lowerBound_transfers_to_right
    (data : IUTStage1BoundedDiscrepancyEquivalent Point f g)
    {B : Real} (hB : ∀ x : Point, B <= f x) :
    ∀ x : Point, B - data.upper <= g x := by
  intro x
  have hbound := hB x
  have hupper := data.upper_bound x
  linarith

theorem lowerBound_transfers_to_left
    (data : IUTStage1BoundedDiscrepancyEquivalent Point f g)
    {B : Real} (hB : ∀ x : Point, B <= g x) :
    ∀ x : Point, B + data.lower <= f x := by
  intro x
  have hbound := hB x
  have hlower := data.lower_bound x
  linarith

theorem upperBound_transfers_to_right
    (data : IUTStage1BoundedDiscrepancyEquivalent Point f g)
    {B : Real} (hB : ∀ x : Point, f x <= B) :
    ∀ x : Point, g x <= B - data.lower := by
  intro x
  have hbound := hB x
  have hlower := data.lower_bound x
  linarith

theorem upperBound_transfers_to_left
    (data : IUTStage1BoundedDiscrepancyEquivalent Point f g)
    {B : Real} (hB : ∀ x : Point, g x <= B) :
    ∀ x : Point, f x <= B + data.upper := by
  intro x
  have hbound := hB x
  have hupper := data.upper_bound x
  linarith

theorem twoSidedBound_transfers_to_right
    (data : IUTStage1BoundedDiscrepancyEquivalent Point f g)
    {L U : Real} (hB : ∀ x : Point, L <= f x ∧ f x <= U) :
    ∀ x : Point, (L - data.upper <= g x) ∧
      (g x <= U - data.lower) := by
  intro x
  exact
    ⟨data.lowerBound_transfers_to_right (fun y => (hB y).1) x,
      data.upperBound_transfers_to_right (fun y => (hB y).2) x⟩

theorem twoSidedBound_transfers_to_left
    (data : IUTStage1BoundedDiscrepancyEquivalent Point f g)
    {L U : Real} (hB : ∀ x : Point, L <= g x ∧ g x <= U) :
    ∀ x : Point, (L + data.lower <= f x) ∧
      (f x <= U + data.upper) := by
  intro x
  exact
    ⟨data.lowerBound_transfers_to_left (fun y => (hB y).1) x,
      data.upperBound_transfers_to_left (fun y => (hB y).2) x⟩

end IUTStage1BoundedDiscrepancyEquivalent

/--
IUT IV, Corollary 2.2(i), bounded-discrepancy chain.

The source records
`(1/6)log(q_2) ≈ (1/6)log(q_all) ≈ (1/6)ht_infty ≈ ht_{omega_X(D)}`.
This record keeps the three adjacent bounded-discrepancy equivalences and proves
the composite relation.
-/
structure IUTStage1IUTIVCorollary22BoundedDiscrepancyChainShadow
    (Point : Type u) where
  logQTwo : Point -> Real
  logQAll : Point -> Real
  heightInfinity : Point -> Real
  canonicalHeight : Point -> Real
  logQTwo_to_logQAll :
    IUTStage1BoundedDiscrepancyEquivalent Point
      (fun x => (1 / 6 : Real) * logQTwo x)
      (fun x => (1 / 6 : Real) * logQAll x)
  logQAll_to_heightInfinity :
    IUTStage1BoundedDiscrepancyEquivalent Point
      (fun x => (1 / 6 : Real) * logQAll x)
      (fun x => (1 / 6 : Real) * heightInfinity x)
  heightInfinity_to_canonicalHeight :
    IUTStage1BoundedDiscrepancyEquivalent Point
      (fun x => (1 / 6 : Real) * heightInfinity x)
      canonicalHeight

namespace IUTStage1IUTIVCorollary22BoundedDiscrepancyChainShadow

variable {Point : Type u}

noncomputable def logQTwo_to_canonicalHeight
    (data :
      IUTStage1IUTIVCorollary22BoundedDiscrepancyChainShadow Point) :
    IUTStage1BoundedDiscrepancyEquivalent Point
      (fun x => (1 / 6 : Real) * data.logQTwo x)
      data.canonicalHeight :=
  IUTStage1BoundedDiscrepancyEquivalent.trans
    (IUTStage1BoundedDiscrepancyEquivalent.trans
      data.logQTwo_to_logQAll data.logQAll_to_heightInfinity)
    data.heightInfinity_to_canonicalHeight

theorem bounded_discrepancy_chain_endpoint
    (data :
      IUTStage1IUTIVCorollary22BoundedDiscrepancyChainShadow Point) :
    Nonempty
        (IUTStage1BoundedDiscrepancyEquivalent Point
          (fun x => (1 / 6 : Real) * data.logQTwo x)
          (fun x => (1 / 6 : Real) * data.logQAll x)) ∧
      Nonempty
        (IUTStage1BoundedDiscrepancyEquivalent Point
          (fun x => (1 / 6 : Real) * data.logQAll x)
          (fun x => (1 / 6 : Real) * data.heightInfinity x)) ∧
      Nonempty
        (IUTStage1BoundedDiscrepancyEquivalent Point
          (fun x => (1 / 6 : Real) * data.heightInfinity x)
          data.canonicalHeight) ∧
      Nonempty
        (IUTStage1BoundedDiscrepancyEquivalent Point
          (fun x => (1 / 6 : Real) * data.logQTwo x)
          data.canonicalHeight) :=
  ⟨⟨data.logQTwo_to_logQAll⟩,
    ⟨data.logQAll_to_heightInfinity⟩,
    ⟨data.heightInfinity_to_canonicalHeight⟩,
    ⟨data.logQTwo_to_canonicalHeight⟩⟩

end IUTStage1IUTIVCorollary22BoundedDiscrepancyChainShadow

/--
IUT IV, Corollary 2.2(ii), condition (C1).

The source records the prime-size window
`(log(q_all))^(1/2) <= l <=
  10 * delta * (log(q_all))^(1/2) * log(2 * delta * log(q_all))`.
This shadow keeps the square-root term as an explicit real parameter, since the
formal construction of `log(q_all)` is not yet present in this file.
-/
structure IUTStage1IUTIVCorollary22C1PrimeScaleWindowShadow where
  l : PrimeGeFive
  delta : Real
  delta_pos : 0 < delta
  logQAll : Real
  sqrtLogQAll : Real
  logTwoDeltaLogQAll : Real
  sqrtLogQAll_nonneg : 0 <= sqrtLogQAll
  sqrtLogQAll_sq_eq_logQAll : sqrtLogQAll ^ 2 = logQAll
  logTwoDeltaLogQAll_ge_one : 1 <= logTwoDeltaLogQAll
  lower_bound :
    sqrtLogQAll <= (l.value : Real)
  upper_bound :
    (l.value : Real) <= 10 * delta * sqrtLogQAll * logTwoDeltaLogQAll

namespace IUTStage1IUTIVCorollary22C1PrimeScaleWindowShadow

theorem l_real_pos
    (data : IUTStage1IUTIVCorollary22C1PrimeScaleWindowShadow) :
    0 < (data.l.value : Real) := by
  exact_mod_cast Nat.pos_of_ne_zero data.l.ne_zero

theorem logQAll_nonneg
    (data : IUTStage1IUTIVCorollary22C1PrimeScaleWindowShadow) :
    0 <= data.logQAll := by
  rw [← data.sqrtLogQAll_sq_eq_logQAll]
  positivity

theorem sqrtLogQAll_le_upperWindow
    (data : IUTStage1IUTIVCorollary22C1PrimeScaleWindowShadow) :
    data.sqrtLogQAll <=
      10 * data.delta * data.sqrtLogQAll * data.logTwoDeltaLogQAll :=
  le_trans data.lower_bound data.upper_bound

theorem upper_window_pos
    (data : IUTStage1IUTIVCorollary22C1PrimeScaleWindowShadow) :
    0 < 10 * data.delta * data.sqrtLogQAll *
      data.logTwoDeltaLogQAll := by
  exact lt_of_lt_of_le data.l_real_pos data.upper_bound

theorem sqrtLogQAll_pos
    (data : IUTStage1IUTIVCorollary22C1PrimeScaleWindowShadow) :
    0 < data.sqrtLogQAll := by
  by_contra hnot
  have hle : data.sqrtLogQAll <= 0 := le_of_not_gt hnot
  have heq : data.sqrtLogQAll = 0 :=
    le_antisymm hle data.sqrtLogQAll_nonneg
  have hupperpos := data.upper_window_pos
  rw [heq, mul_zero, zero_mul] at hupperpos
  exact (lt_irrefl (0 : Real)) hupperpos

theorem one_le_ten_delta_logFactor
    (data : IUTStage1IUTIVCorollary22C1PrimeScaleWindowShadow) :
    (1 : Real) <= 10 * data.delta * data.logTwoDeltaLogQAll := by
  have hpos := data.sqrtLogQAll_pos
  have hwindow := data.sqrtLogQAll_le_upperWindow
  have hdiv :
      data.sqrtLogQAll / data.sqrtLogQAll <=
        10 * data.delta * data.logTwoDeltaLogQAll := by
    rw [div_le_iff₀ hpos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hwindow
  have hself : data.sqrtLogQAll / data.sqrtLogQAll = 1 :=
    div_self (ne_of_gt hpos)
  linarith

theorem c1_prime_scale_window_endpoint
    (data : IUTStage1IUTIVCorollary22C1PrimeScaleWindowShadow) :
    data.sqrtLogQAll <= (data.l.value : Real) ∧
      (data.l.value : Real) <=
        10 * data.delta * data.sqrtLogQAll * data.logTwoDeltaLogQAll ∧
      0 < data.sqrtLogQAll ∧
      0 <= data.logQAll ∧
      (1 : Real) <= 10 * data.delta * data.logTwoDeltaLogQAll :=
  ⟨data.lower_bound,
    data.upper_bound,
    data.sqrtLogQAll_pos,
    data.logQAll_nonneg,
    data.one_le_ten_delta_logFactor⟩

end IUTStage1IUTIVCorollary22C1PrimeScaleWindowShadow

/--
IUT IV, Corollary 2.2(ii), use of condition (C1) in the Theorem 1.10
coefficient.

The proof applies the lower part of (C1), together with the source estimate
`20 * d_mod <= delta`, to replace `20 * d_mod / l` by `delta * h^(-1/2)`.
-/
structure IUTStage1IUTIVCorollary22C1Theorem110CoefficientShadow where
  l : PrimeGeFive
  dmod : Nat
  delta : Real
  sqrtH : Real
  sqrtH_pos : 0 < sqrtH
  sqrtH_le_l : sqrtH <= (l.value : Real)
  twenty_dmod_le_delta : 20 * (dmod : Real) <= delta

namespace IUTStage1IUTIVCorollary22C1Theorem110CoefficientShadow

theorem l_real_pos
    (data : IUTStage1IUTIVCorollary22C1Theorem110CoefficientShadow) :
    0 < (data.l.value : Real) := by
  exact_mod_cast Nat.pos_of_ne_zero data.l.ne_zero

theorem delta_nonneg
    (data : IUTStage1IUTIVCorollary22C1Theorem110CoefficientShadow) :
    0 <= data.delta := by
  have hdmod : 0 <= 20 * (data.dmod : Real) := by positivity
  linarith [data.twenty_dmod_le_delta]

theorem coefficient_le_delta_inv_sqrtH
    (data : IUTStage1IUTIVCorollary22C1Theorem110CoefficientShadow) :
    20 * (data.dmod : Real) / (data.l.value : Real) <=
      data.delta / data.sqrtH := by
  have h_l_pos := data.l_real_pos
  have hfirst :
      20 * (data.dmod : Real) / (data.l.value : Real) <=
        data.delta / (data.l.value : Real) :=
    div_le_div_of_nonneg_right data.twenty_dmod_le_delta h_l_pos.le
  have hsecond :
      data.delta / (data.l.value : Real) <= data.delta / data.sqrtH :=
    div_le_div_of_nonneg_left data.delta_nonneg data.sqrtH_pos data.sqrtH_le_l
  exact le_trans hfirst hsecond

theorem one_add_coefficient_le_one_add_delta_inv_sqrtH
    (data : IUTStage1IUTIVCorollary22C1Theorem110CoefficientShadow) :
    1 + 20 * (data.dmod : Real) / (data.l.value : Real) <=
      1 + data.delta / data.sqrtH := by
  linarith [data.coefficient_le_delta_inv_sqrtH]

theorem coefficient_replacement_endpoint
    (data : IUTStage1IUTIVCorollary22C1Theorem110CoefficientShadow) :
    0 < (data.l.value : Real) ∧
      0 < data.sqrtH ∧
      0 <= data.delta ∧
      20 * (data.dmod : Real) / (data.l.value : Real) <=
        data.delta / data.sqrtH ∧
      1 + 20 * (data.dmod : Real) / (data.l.value : Real) <=
        1 + data.delta / data.sqrtH :=
  ⟨data.l_real_pos,
    data.sqrtH_pos,
    data.delta_nonneg,
    data.coefficient_le_delta_inv_sqrtH,
    data.one_add_coefficient_le_one_add_delta_inv_sqrtH⟩

end IUTStage1IUTIVCorollary22C1Theorem110CoefficientShadow

/--
IUT IV, Corollary 2.2(ii), use of the upper part of (C1) in the Theorem 1.10
error term.

The proof combines `d^*_mod <= delta` with
`l <= 10 * delta * h^(1/2) * log(2 * delta * h)`.
-/
structure IUTStage1IUTIVCorollary22C1ErrorTermShadow where
  l : PrimeGeFive
  dStarMod : Real
  delta : Real
  sqrtH : Real
  logTwoDeltaH : Real
  etaPrm : Real
  dStarMod_nonneg : 0 <= dStarMod
  delta_nonneg : 0 <= delta
  sqrtH_nonneg : 0 <= sqrtH
  logTwoDeltaH_nonneg : 0 <= logTwoDeltaH
  dStarMod_le_delta : dStarMod <= delta
  l_upper_bound :
    (l.value : Real) <= 10 * delta * sqrtH * logTwoDeltaH

namespace IUTStage1IUTIVCorollary22C1ErrorTermShadow

theorem l_real_nonneg
    (data : IUTStage1IUTIVCorollary22C1ErrorTermShadow) :
    0 <= (data.l.value : Real) := by
  exact_mod_cast Nat.zero_le data.l.value

theorem dStarMod_mul_l_le_delta_window
    (data : IUTStage1IUTIVCorollary22C1ErrorTermShadow) :
    data.dStarMod * (data.l.value : Real) <=
      data.delta * (10 * data.delta * data.sqrtH * data.logTwoDeltaH) :=
  mul_le_mul data.dStarMod_le_delta data.l_upper_bound data.l_real_nonneg
    data.delta_nonneg

theorem theorem110_errorTerm_le_corollary22_errorTerm
    (data : IUTStage1IUTIVCorollary22C1ErrorTermShadow) :
    20 * (data.dStarMod * (data.l.value : Real) + data.etaPrm) <=
      200 * data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH +
        20 * data.etaPrm := by
  have hprod := data.dStarMod_mul_l_le_delta_window
  have hscaled :
      20 * (data.dStarMod * (data.l.value : Real)) <=
        20 * (data.delta * (10 * data.delta * data.sqrtH *
          data.logTwoDeltaH)) := by
    exact mul_le_mul_of_nonneg_left hprod (by norm_num)
  calc
    20 * (data.dStarMod * (data.l.value : Real) + data.etaPrm)
        =
      20 * (data.dStarMod * (data.l.value : Real)) + 20 * data.etaPrm := by
        ring
    _ <=
      20 * (data.delta * (10 * data.delta * data.sqrtH *
        data.logTwoDeltaH)) + 20 * data.etaPrm := by
        exact add_le_add hscaled le_rfl
    _ =
      200 * data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH +
        20 * data.etaPrm := by
        ring

theorem errorTerm_replacement_endpoint
    (data : IUTStage1IUTIVCorollary22C1ErrorTermShadow) :
    0 <= (data.l.value : Real) ∧
      0 <= data.dStarMod ∧
      0 <= data.delta ∧
      0 <= data.sqrtH ∧
      0 <= data.logTwoDeltaH ∧
      data.dStarMod <= data.delta ∧
      (data.l.value : Real) <=
        10 * data.delta * data.sqrtH * data.logTwoDeltaH ∧
      data.dStarMod * (data.l.value : Real) <=
        data.delta * (10 * data.delta * data.sqrtH * data.logTwoDeltaH) ∧
      20 * (data.dStarMod * (data.l.value : Real) + data.etaPrm) <=
        200 * data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH +
          20 * data.etaPrm :=
  ⟨data.l_real_nonneg,
    data.dStarMod_nonneg,
    data.delta_nonneg,
    data.sqrtH_nonneg,
    data.logTwoDeltaH_nonneg,
    data.dStarMod_le_delta,
    data.l_upper_bound,
    data.dStarMod_mul_l_le_delta_window,
    data.theorem110_errorTerm_le_corollary22_errorTerm⟩

end IUTStage1IUTIVCorollary22C1ErrorTermShadow

/--
IUT IV, Corollary 2.2(ii), first inequality after applying Theorem 1.10.

This composes the Theorem 1.10 bound with the two C1-based replacements:
`20*d_mod/l <= delta*h^(-1/2)` and
`20*(d^*_mod*l + eta_prm) <=
  200*delta^2*h^(1/2)*log(2*delta*h) + 20*eta_prm`.
-/
structure IUTStage1IUTIVCorollary22Theorem110ToC2FirstBoundShadow where
  l : PrimeGeFive
  dmod : Nat
  dStarMod : Real
  delta : Real
  sqrtH : Real
  logTwoDeltaH : Real
  etaPrm : Real
  logQ : Real
  logDegreeSum : Real
  sqrtH_pos : 0 < sqrtH
  sqrtH_le_l : sqrtH <= (l.value : Real)
  twenty_dmod_le_delta : 20 * (dmod : Real) <= delta
  dStarMod_nonneg : 0 <= dStarMod
  delta_nonneg : 0 <= delta
  logTwoDeltaH_nonneg : 0 <= logTwoDeltaH
  dStarMod_le_delta : dStarMod <= delta
  l_upper_bound :
    (l.value : Real) <= 10 * delta * sqrtH * logTwoDeltaH
  logDegreeSum_nonneg : 0 <= logDegreeSum
  theorem110_bound :
    (1 / 6 : Real) * logQ <=
      (1 + 20 * (dmod : Real) / (l.value : Real)) * logDegreeSum +
        20 * (dStarMod * (l.value : Real) + etaPrm)

namespace IUTStage1IUTIVCorollary22Theorem110ToC2FirstBoundShadow

def coefficientShadow
    (data : IUTStage1IUTIVCorollary22Theorem110ToC2FirstBoundShadow) :
    IUTStage1IUTIVCorollary22C1Theorem110CoefficientShadow :=
  { l := data.l
    dmod := data.dmod
    delta := data.delta
    sqrtH := data.sqrtH
    sqrtH_pos := data.sqrtH_pos
    sqrtH_le_l := data.sqrtH_le_l
    twenty_dmod_le_delta := data.twenty_dmod_le_delta }

def errorTermShadow
    (data : IUTStage1IUTIVCorollary22Theorem110ToC2FirstBoundShadow) :
    IUTStage1IUTIVCorollary22C1ErrorTermShadow :=
  { l := data.l
    dStarMod := data.dStarMod
    delta := data.delta
    sqrtH := data.sqrtH
    logTwoDeltaH := data.logTwoDeltaH
    etaPrm := data.etaPrm
    dStarMod_nonneg := data.dStarMod_nonneg
    delta_nonneg := data.delta_nonneg
    sqrtH_nonneg := data.sqrtH_pos.le
    logTwoDeltaH_nonneg := data.logTwoDeltaH_nonneg
    dStarMod_le_delta := data.dStarMod_le_delta
    l_upper_bound := data.l_upper_bound }

theorem oneSixthLogQ_le_corollary22FirstRightHandSide
    (data : IUTStage1IUTIVCorollary22Theorem110ToC2FirstBoundShadow) :
    (1 / 6 : Real) * data.logQ <=
      (1 + data.delta / data.sqrtH) * data.logDegreeSum +
        (200 * data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH +
          20 * data.etaPrm) := by
  have hcoeff :=
    data.coefficientShadow.one_add_coefficient_le_one_add_delta_inv_sqrtH
  have hcoeff_mul :
      (1 + 20 * (data.dmod : Real) / (data.l.value : Real)) *
          data.logDegreeSum <=
        (1 + data.delta / data.sqrtH) * data.logDegreeSum :=
    mul_le_mul_of_nonneg_right hcoeff data.logDegreeSum_nonneg
  have herr :=
    data.errorTermShadow.theorem110_errorTerm_le_corollary22_errorTerm
  calc
    (1 / 6 : Real) * data.logQ <=
      (1 + 20 * (data.dmod : Real) / (data.l.value : Real)) *
          data.logDegreeSum +
        20 * (data.dStarMod * (data.l.value : Real) + data.etaPrm) :=
          data.theorem110_bound
    _ <=
      (1 + data.delta / data.sqrtH) * data.logDegreeSum +
        (200 * data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH +
          20 * data.etaPrm) :=
          add_le_add hcoeff_mul herr

end IUTStage1IUTIVCorollary22Theorem110ToC2FirstBoundShadow

/--
IUT IV, Corollary 2.2(ii), the displayed estimate comparing `log(q_2)` and
`log(q)`.

The source obtains
`(1/6)log(q_2) - (1/6)log(q) <=
  (1/3) * h^(1/2) * log(2 * delta * h)`
through the intermediate term `h^(1/2) * log(l)`.
-/
structure IUTStage1IUTIVCorollary22QTwoMinusQBoundShadow where
  logQ : Real
  logQTwo : Real
  sqrtH : Real
  logL : Real
  logTwoDeltaH : Real
  sqrtH_nonneg : 0 <= sqrtH
  qTwo_minus_q_le_oneSixth_sqrtH :
    (1 / 6 : Real) * logQTwo - (1 / 6 : Real) * logQ <=
      (1 / 6 : Real) * sqrtH
  one_le_six_logL : 1 <= 6 * logL
  three_logL_le_logTwoDeltaH : 3 * logL <= logTwoDeltaH

namespace IUTStage1IUTIVCorollary22QTwoMinusQBoundShadow

theorem oneSixth_sqrtH_le_sqrtH_logL
    (data : IUTStage1IUTIVCorollary22QTwoMinusQBoundShadow) :
    (1 / 6 : Real) * data.sqrtH <= data.sqrtH * data.logL := by
  have hcoeff : (1 / 6 : Real) <= data.logL := by
    linarith [data.one_le_six_logL]
  calc
    (1 / 6 : Real) * data.sqrtH <= data.logL * data.sqrtH :=
      mul_le_mul_of_nonneg_right hcoeff data.sqrtH_nonneg
    _ = data.sqrtH * data.logL := by ring

theorem sqrtH_logL_le_oneThird_sqrtH_logTwoDeltaH
    (data : IUTStage1IUTIVCorollary22QTwoMinusQBoundShadow) :
    data.sqrtH * data.logL <=
      (1 / 3 : Real) * data.sqrtH * data.logTwoDeltaH := by
  have hcoeff : data.logL <= (1 / 3 : Real) * data.logTwoDeltaH := by
    linarith [data.three_logL_le_logTwoDeltaH]
  calc
    data.sqrtH * data.logL <= data.sqrtH *
        ((1 / 3 : Real) * data.logTwoDeltaH) :=
      mul_le_mul_of_nonneg_left hcoeff data.sqrtH_nonneg
    _ = (1 / 3 : Real) * data.sqrtH * data.logTwoDeltaH := by ring

theorem qTwo_minus_q_le_oneThird_sqrtH_logTwoDeltaH
    (data : IUTStage1IUTIVCorollary22QTwoMinusQBoundShadow) :
    (1 / 6 : Real) * data.logQTwo - (1 / 6 : Real) * data.logQ <=
      (1 / 3 : Real) * data.sqrtH * data.logTwoDeltaH :=
  le_trans data.qTwo_minus_q_le_oneSixth_sqrtH
    (le_trans data.oneSixth_sqrtH_le_sqrtH_logL
      data.sqrtH_logL_le_oneThird_sqrtH_logTwoDeltaH)

theorem qTwo_minus_q_endpoint
    (data : IUTStage1IUTIVCorollary22QTwoMinusQBoundShadow) :
    0 <= data.sqrtH ∧
      (1 / 6 : Real) * data.logQTwo - (1 / 6 : Real) * data.logQ <=
        (1 / 6 : Real) * data.sqrtH ∧
      1 <= 6 * data.logL ∧
      3 * data.logL <= data.logTwoDeltaH ∧
      (1 / 6 : Real) * data.sqrtH <= data.sqrtH * data.logL ∧
      data.sqrtH * data.logL <=
        (1 / 3 : Real) * data.sqrtH * data.logTwoDeltaH ∧
      (1 / 6 : Real) * data.logQTwo - (1 / 6 : Real) * data.logQ <=
        (1 / 3 : Real) * data.sqrtH * data.logTwoDeltaH :=
  ⟨data.sqrtH_nonneg,
    data.qTwo_minus_q_le_oneSixth_sqrtH,
    data.one_le_six_logL,
    data.three_logL_le_logTwoDeltaH,
    data.oneSixth_sqrtH_le_sqrtH_logL,
    data.sqrtH_logL_le_oneThird_sqrtH_logTwoDeltaH,
    data.qTwo_minus_q_le_oneThird_sqrtH_logTwoDeltaH⟩

end IUTStage1IUTIVCorollary22QTwoMinusQBoundShadow

/--
IUT IV, Corollary 2.2(ii), passage from the Theorem 1.10 bound for `q` to the
displayed bound for `h = log(q_all)`.

This combines the first post-Theorem-1.10 bound, the `q_2/q` estimate, and the
bounded discrepancy `q_all/q_2` constant `B_K`, with
`C_K = 40 * eta_prm + 2 * B_K`.
-/
structure IUTStage1IUTIVCorollary22HBoundBeforeEpsilonShadow where
  h : Real
  logQ : Real
  logQTwo : Real
  logQAll : Real
  logDegreeSum : Real
  delta : Real
  sqrtH : Real
  logTwoDeltaH : Real
  etaPrm : Real
  bK : Real
  cK : Real
  h_eq_logQAll : h = logQAll
  delta_ge_one : 1 <= delta
  sqrtH_logTwoDeltaH_nonneg : 0 <= sqrtH * logTwoDeltaH
  cK_eq : cK = 40 * etaPrm + 2 * bK
  theorem110_first_bound :
    (1 / 6 : Real) * logQ <=
      (1 + delta / sqrtH) * logDegreeSum +
        (200 * delta ^ 2 * sqrtH * logTwoDeltaH + 20 * etaPrm)
  qTwo_minus_q_bound :
    (1 / 6 : Real) * logQTwo - (1 / 6 : Real) * logQ <=
      (1 / 3 : Real) * sqrtH * logTwoDeltaH
  qAll_minus_qTwo_bound :
    (1 / 6 : Real) * logQAll - (1 / 6 : Real) * logQTwo <= bK

namespace IUTStage1IUTIVCorollary22HBoundBeforeEpsilonShadow

theorem error_terms_le_fifteen_delta_sq
    (data : IUTStage1IUTIVCorollary22HBoundBeforeEpsilonShadow) :
    200 * data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH +
        (1 / 3 : Real) * data.sqrtH * data.logTwoDeltaH <=
      (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH := by
  have hdelta_sq : (1 / 3 : Real) <= 25 * data.delta ^ 2 := by
    nlinarith [data.delta_ge_one]
  have hA := data.sqrtH_logTwoDeltaH_nonneg
  calc
    200 * data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH +
        (1 / 3 : Real) * data.sqrtH * data.logTwoDeltaH
        =
      (200 * data.delta ^ 2 + (1 / 3 : Real)) *
        (data.sqrtH * data.logTwoDeltaH) := by ring
    _ <=
      (200 * data.delta ^ 2 + 25 * data.delta ^ 2) *
        (data.sqrtH * data.logTwoDeltaH) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hA
    _ =
      (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH := by ring

theorem cK_half_eq_eta_bK
    (data : IUTStage1IUTIVCorollary22HBoundBeforeEpsilonShadow) :
    (1 / 2 : Real) * data.cK = 20 * data.etaPrm + data.bK := by
  rw [data.cK_eq]
  ring

theorem logQTwo_le_logQ_add_qTwoError
    (data : IUTStage1IUTIVCorollary22HBoundBeforeEpsilonShadow) :
    (1 / 6 : Real) * data.logQTwo <=
      (1 / 6 : Real) * data.logQ +
        (1 / 3 : Real) * data.sqrtH * data.logTwoDeltaH := by
  linarith [data.qTwo_minus_q_bound]

theorem logQAll_le_logQTwo_add_bK
    (data : IUTStage1IUTIVCorollary22HBoundBeforeEpsilonShadow) :
    (1 / 6 : Real) * data.logQAll <=
      (1 / 6 : Real) * data.logQTwo + data.bK := by
  linarith [data.qAll_minus_qTwo_bound]

theorem logQAll_le_theorem110_with_discrepancy
    (data : IUTStage1IUTIVCorollary22HBoundBeforeEpsilonShadow) :
    (1 / 6 : Real) * data.logQAll <=
      (1 + data.delta / data.sqrtH) * data.logDegreeSum +
        (200 * data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH +
          20 * data.etaPrm) +
          (1 / 3 : Real) * data.sqrtH * data.logTwoDeltaH +
          data.bK := by
  linarith [data.theorem110_first_bound,
    data.logQTwo_le_logQ_add_qTwoError,
    data.logQAll_le_logQTwo_add_bK]

theorem h_bound_before_epsilon
    (data : IUTStage1IUTIVCorollary22HBoundBeforeEpsilonShadow) :
    (1 / 6 : Real) * data.h <=
      (1 + data.delta / data.sqrtH) * data.logDegreeSum +
        (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH +
          (1 / 2 : Real) * data.cK := by
  have herr := data.error_terms_le_fifteen_delta_sq
  calc
    (1 / 6 : Real) * data.h =
        (1 / 6 : Real) * data.logQAll := by rw [data.h_eq_logQAll]
    _ <=
        (1 + data.delta / data.sqrtH) * data.logDegreeSum +
          (200 * data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH +
            20 * data.etaPrm) +
            (1 / 3 : Real) * data.sqrtH * data.logTwoDeltaH +
            data.bK := data.logQAll_le_theorem110_with_discrepancy
    _ <=
        (1 + data.delta / data.sqrtH) * data.logDegreeSum +
          (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH +
            (20 * data.etaPrm + data.bK) := by
        linarith [herr]
    _ =
        (1 + data.delta / data.sqrtH) * data.logDegreeSum +
          (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH +
          (1 / 2 : Real) * data.cK := by
        rw [data.cK_half_eq_eta_bK]

theorem h_bound_before_epsilon_endpoint
    (data : IUTStage1IUTIVCorollary22HBoundBeforeEpsilonShadow) :
    data.h = data.logQAll ∧
      1 <= data.delta ∧
      0 <= data.sqrtH * data.logTwoDeltaH ∧
      data.cK = 40 * data.etaPrm + 2 * data.bK ∧
      (1 / 6 : Real) * data.logQ <=
        (1 + data.delta / data.sqrtH) * data.logDegreeSum +
          (200 * data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH +
            20 * data.etaPrm) ∧
      (1 / 6 : Real) * data.logQTwo <=
        (1 / 6 : Real) * data.logQ +
          (1 / 3 : Real) * data.sqrtH * data.logTwoDeltaH ∧
      (1 / 6 : Real) * data.logQAll <=
        (1 / 6 : Real) * data.logQTwo + data.bK ∧
      200 * data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH +
          (1 / 3 : Real) * data.sqrtH * data.logTwoDeltaH <=
        (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH ∧
      (1 / 2 : Real) * data.cK = 20 * data.etaPrm + data.bK ∧
      (1 / 6 : Real) * data.h <=
        (1 + data.delta / data.sqrtH) * data.logDegreeSum +
          (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH +
            (1 / 2 : Real) * data.cK :=
  ⟨data.h_eq_logQAll,
    data.delta_ge_one,
    data.sqrtH_logTwoDeltaH_nonneg,
    data.cK_eq,
    data.theorem110_first_bound,
    data.logQTwo_le_logQ_add_qTwoError,
    data.logQAll_le_logQTwo_add_bK,
    data.error_terms_le_fifteen_delta_sq,
    data.cK_half_eq_eta_bK,
    data.h_bound_before_epsilon⟩

end IUTStage1IUTIVCorollary22HBoundBeforeEpsilonShadow

/--
IUT IV, Corollary 2.2(ii), condition (C2).

The source records the chain
`(1/6)log(q) <= (1/6)log(q_2) <= (1/6)log(q_all) <=
(1+epsilon_E)*(log-diff_X(x_E)+log-cond_D(x_E))+C_K`.
This record keeps exactly that real-valued inequality chain.
-/
structure IUTStage1IUTIVCorollary22C2InequalityChainShadow where
  logQ : Real
  logQTwo : Real
  logQAll : Real
  epsilonE : Real
  logDiffX : Real
  logCondD : Real
  cK : Real
  logQ_le_logQTwo :
    (1 / 6 : Real) * logQ <= (1 / 6 : Real) * logQTwo
  logQTwo_le_logQAll :
    (1 / 6 : Real) * logQTwo <= (1 / 6 : Real) * logQAll
  logQAll_le_heightSide :
    (1 / 6 : Real) * logQAll <=
      (1 + epsilonE) * (logDiffX + logCondD) + cK

namespace IUTStage1IUTIVCorollary22C2InequalityChainShadow

noncomputable def heightSide
    (data : IUTStage1IUTIVCorollary22C2InequalityChainShadow) : Real :=
  (1 + data.epsilonE) * (data.logDiffX + data.logCondD) + data.cK

theorem logQ_le_heightSide
    (data : IUTStage1IUTIVCorollary22C2InequalityChainShadow) :
    (1 / 6 : Real) * data.logQ <= data.heightSide :=
  le_trans data.logQ_le_logQTwo
    (le_trans data.logQTwo_le_logQAll data.logQAll_le_heightSide)

theorem logQTwo_le_heightSide
    (data : IUTStage1IUTIVCorollary22C2InequalityChainShadow) :
    (1 / 6 : Real) * data.logQTwo <= data.heightSide :=
  le_trans data.logQTwo_le_logQAll data.logQAll_le_heightSide

end IUTStage1IUTIVCorollary22C2InequalityChainShadow

/--
The `epsilon_E` expression introduced in the proof of IUT IV, Corollary 2.2(ii):
`(60 * delta)^2 * h^(-1/2) * log(2 * delta * h)`.

The square-root of `h = log(q_all)` and the logarithmic factor are explicit
parameters at this stage.
-/
noncomputable def iutIVCorollary22EpsilonDefinitionRHS
    (delta sqrtH logTwoDeltaH : Real) : Real :=
  (60 * delta) ^ 2 * sqrtH⁻¹ * logTwoDeltaH

/--
IUT IV, Corollary 2.2(ii), definition and elementary lower estimate for
`epsilon_E`.

The source records
`epsilon_E := (60 delta)^2 h^(-1/2) log(2 delta h) (>= 5 delta h^(-1/2))`,
using `delta >= 2` and `log(2 delta h) >= 1`.
-/
structure IUTStage1IUTIVCorollary22EpsilonDefinitionShadow where
  delta : Real
  sqrtH : Real
  logTwoDeltaH : Real
  epsilonE : Real
  delta_ge_two : 2 <= delta
  sqrtH_pos : 0 < sqrtH
  logTwoDeltaH_ge_one : 1 <= logTwoDeltaH
  epsilonE_eq :
    epsilonE =
      iutIVCorollary22EpsilonDefinitionRHS delta sqrtH logTwoDeltaH

namespace IUTStage1IUTIVCorollary22EpsilonDefinitionShadow

theorem delta_pos
    (data : IUTStage1IUTIVCorollary22EpsilonDefinitionShadow) :
    0 < data.delta := by
  linarith [data.delta_ge_two]

theorem epsilonE_pos
    (data : IUTStage1IUTIVCorollary22EpsilonDefinitionShadow) :
    0 < data.epsilonE := by
  rw [data.epsilonE_eq, iutIVCorollary22EpsilonDefinitionRHS]
  have hsixty_delta : 0 < 60 * data.delta := by
    nlinarith [data.delta_pos]
  have hsquare : 0 < (60 * data.delta) ^ 2 :=
    sq_pos_of_pos hsixty_delta
  have hinv : 0 < data.sqrtH⁻¹ := inv_pos.mpr data.sqrtH_pos
  have hlog : 0 < data.logTwoDeltaH := by
    linarith [data.logTwoDeltaH_ge_one]
  exact mul_pos (mul_pos hsquare hinv) hlog

theorem five_delta_inv_sqrtH_le_epsilonE
    (data : IUTStage1IUTIVCorollary22EpsilonDefinitionShadow) :
    5 * data.delta * data.sqrtH⁻¹ <= data.epsilonE := by
  rw [data.epsilonE_eq, iutIVCorollary22EpsilonDefinitionRHS]
  have hsquare_nonneg : 0 <= (60 * data.delta) ^ 2 := sq_nonneg _
  have hlogmul :
      (60 * data.delta) ^ 2 <=
        (60 * data.delta) ^ 2 * data.logTwoDeltaH := by
    simpa using
      mul_le_mul_of_nonneg_left data.logTwoDeltaH_ge_one hsquare_nonneg
  have hmain : 5 * data.delta <=
      (60 * data.delta) ^ 2 * data.logTwoDeltaH := by
    have hdelta_pos := data.delta_pos
    nlinarith [data.delta_ge_two, hlogmul]
  have hinv_nonneg : 0 <= data.sqrtH⁻¹ := inv_nonneg.mpr data.sqrtH_pos.le
  have hmul :=
    mul_le_mul_of_nonneg_right hmain hinv_nonneg
  calc
    5 * data.delta * data.sqrtH⁻¹ =
        (5 * data.delta) * data.sqrtH⁻¹ := by ring
    _ <= ((60 * data.delta) ^ 2 * data.logTwoDeltaH) * data.sqrtH⁻¹ :=
        hmul
    _ = (60 * data.delta) ^ 2 * data.sqrtH⁻¹ * data.logTwoDeltaH := by
        ring

theorem five_delta_inv_sqrtH_le_one_of_epsilonE_le_one
    (data : IUTStage1IUTIVCorollary22EpsilonDefinitionShadow)
    (heps : data.epsilonE <= 1) :
    5 * data.delta * data.sqrtH⁻¹ <= 1 :=
  le_trans data.five_delta_inv_sqrtH_le_epsilonE heps

theorem epsilon_definition_endpoint
    (data : IUTStage1IUTIVCorollary22EpsilonDefinitionShadow) :
    2 <= data.delta ∧
      0 < data.delta ∧
      0 < data.sqrtH ∧
      1 <= data.logTwoDeltaH ∧
      data.epsilonE =
        iutIVCorollary22EpsilonDefinitionRHS
          data.delta data.sqrtH data.logTwoDeltaH ∧
      0 < data.epsilonE ∧
      5 * data.delta * data.sqrtH⁻¹ <= data.epsilonE :=
  ⟨data.delta_ge_two,
    data.delta_pos,
    data.sqrtH_pos,
    data.logTwoDeltaH_ge_one,
    data.epsilonE_eq,
    data.epsilonE_pos,
    data.five_delta_inv_sqrtH_le_epsilonE⟩

end IUTStage1IUTIVCorollary22EpsilonDefinitionShadow

/--
IUT IV, Corollary 2.2(ii), conversion of the pre-`epsilon_E` error term.

The proof rewrites the term `(15 * delta)^2 * h^(1/2) * log(2 * delta * h)` as
bounded by `(1/6) * h * (2/5 * epsilon_E)` after substituting the definition of
`epsilon_E`.
-/
structure IUTStage1IUTIVCorollary22EpsilonErrorConversionShadow where
  h : Real
  delta : Real
  sqrtH : Real
  logTwoDeltaH : Real
  epsilonE : Real
  sqrtH_pos : 0 < sqrtH
  delta_sq_log_nonneg : 0 <= delta ^ 2 * logTwoDeltaH
  h_eq_sqrtH_sq : h = sqrtH ^ 2
  epsilonE_eq :
    epsilonE =
      iutIVCorollary22EpsilonDefinitionRHS delta sqrtH logTwoDeltaH

namespace IUTStage1IUTIVCorollary22EpsilonErrorConversionShadow

theorem fifteen_delta_sq_error_le_epsilon_term
    (data : IUTStage1IUTIVCorollary22EpsilonErrorConversionShadow) :
    (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH <=
      (1 / 6 : Real) * data.h * ((2 / 5 : Real) * data.epsilonE) := by
  have hleft_nonneg :
      0 <= data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH := by
    have h := mul_nonneg data.delta_sq_log_nonneg data.sqrtH_pos.le
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  rw [data.h_eq_sqrtH_sq, data.epsilonE_eq,
    iutIVCorollary22EpsilonDefinitionRHS]
  have hsqrt_ne : data.sqrtH ≠ 0 := ne_of_gt data.sqrtH_pos
  have hcancel :
      data.sqrtH ^ 2 * ((data.sqrtH)⁻¹) = data.sqrtH := by
    field_simp [hsqrt_ne]
  calc
    (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH
        =
      225 * (data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH) := by ring
    _ <=
      240 * (data.delta ^ 2 * data.sqrtH * data.logTwoDeltaH) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) hleft_nonneg
    _ =
      (1 / 6 : Real) * data.sqrtH ^ 2 *
        ((2 / 5 : Real) *
          ((60 * data.delta) ^ 2 * data.sqrtH⁻¹ * data.logTwoDeltaH)) := by
        field_simp [hsqrt_ne]
        ring

theorem epsilon_error_conversion_endpoint
    (data : IUTStage1IUTIVCorollary22EpsilonErrorConversionShadow) :
    0 < data.sqrtH ∧
      0 <= data.delta ^ 2 * data.logTwoDeltaH ∧
      data.h = data.sqrtH ^ 2 ∧
      data.epsilonE =
        iutIVCorollary22EpsilonDefinitionRHS
          data.delta data.sqrtH data.logTwoDeltaH ∧
      (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH <=
        (1 / 6 : Real) * data.h * ((2 / 5 : Real) * data.epsilonE) :=
  ⟨data.sqrtH_pos,
    data.delta_sq_log_nonneg,
    data.h_eq_sqrtH_sq,
    data.epsilonE_eq,
    data.fifteen_delta_sq_error_le_epsilon_term⟩

end IUTStage1IUTIVCorollary22EpsilonErrorConversionShadow

/--
IUT IV, Corollary 2.2(ii), bridge from the pre-`epsilon_E` bound to the
preliminary inequality used in the denominator step.

This combines `epsilon_E >= 5 * delta * h^(-1/2)` with the preceding conversion
of the `(15 * delta)^2` error term.
-/
structure IUTStage1IUTIVCorollary22HBoundToMoveLeftShadow where
  h : Real
  logDegreeSum : Real
  cK : Real
  delta : Real
  sqrtH : Real
  logTwoDeltaH : Real
  epsilonE : Real
  logDegreeSum_nonneg : 0 <= logDegreeSum
  delta_inv_sqrtH_le_epsilon_over_five :
    delta / sqrtH <= (1 / 5 : Real) * epsilonE
  error_conversion_bound :
    (15 * delta) ^ 2 * sqrtH * logTwoDeltaH <=
      (1 / 6 : Real) * h * ((2 / 5 : Real) * epsilonE)
  pre_epsilon_bound :
    (1 / 6 : Real) * h <=
      (1 + delta / sqrtH) * logDegreeSum +
        (15 * delta) ^ 2 * sqrtH * logTwoDeltaH +
          (1 / 2 : Real) * cK

namespace IUTStage1IUTIVCorollary22HBoundToMoveLeftShadow

theorem coefficient_le_epsilon_coefficient
    (data : IUTStage1IUTIVCorollary22HBoundToMoveLeftShadow) :
    1 + data.delta / data.sqrtH <=
      1 + (1 / 5 : Real) * data.epsilonE := by
  linarith [data.delta_inv_sqrtH_le_epsilon_over_five]

theorem preliminary_for_move_left
    (data : IUTStage1IUTIVCorollary22HBoundToMoveLeftShadow) :
    (1 / 6 : Real) * data.h <=
      (1 + (1 / 5 : Real) * data.epsilonE) * data.logDegreeSum +
        (1 / 6 : Real) * data.h * ((2 / 5 : Real) * data.epsilonE) +
          (1 / 2 : Real) * data.cK := by
  have hcoeff := data.coefficient_le_epsilon_coefficient
  have hcoeff_mul :
      (1 + data.delta / data.sqrtH) * data.logDegreeSum <=
        (1 + (1 / 5 : Real) * data.epsilonE) * data.logDegreeSum :=
    mul_le_mul_of_nonneg_right hcoeff data.logDegreeSum_nonneg
  calc
    (1 / 6 : Real) * data.h <=
      (1 + data.delta / data.sqrtH) * data.logDegreeSum +
        (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH +
          (1 / 2 : Real) * data.cK :=
          data.pre_epsilon_bound
    _ <=
      (1 + (1 / 5 : Real) * data.epsilonE) * data.logDegreeSum +
        (1 / 6 : Real) * data.h * ((2 / 5 : Real) * data.epsilonE) +
          (1 / 2 : Real) * data.cK :=
          add_le_add (add_le_add hcoeff_mul data.error_conversion_bound) le_rfl

theorem h_bound_to_move_left_endpoint
    (data : IUTStage1IUTIVCorollary22HBoundToMoveLeftShadow) :
    0 <= data.logDegreeSum ∧
      data.delta / data.sqrtH <= (1 / 5 : Real) * data.epsilonE ∧
      (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH <=
        (1 / 6 : Real) * data.h * ((2 / 5 : Real) * data.epsilonE) ∧
      (1 / 6 : Real) * data.h <=
        (1 + data.delta / data.sqrtH) * data.logDegreeSum +
          (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH +
            (1 / 2 : Real) * data.cK ∧
      1 + data.delta / data.sqrtH <=
        1 + (1 / 5 : Real) * data.epsilonE ∧
      (1 / 6 : Real) * data.h <=
        (1 + (1 / 5 : Real) * data.epsilonE) * data.logDegreeSum +
          (1 / 6 : Real) * data.h * ((2 / 5 : Real) * data.epsilonE) +
            (1 / 2 : Real) * data.cK :=
  ⟨data.logDegreeSum_nonneg,
    data.delta_inv_sqrtH_le_epsilon_over_five,
    data.error_conversion_bound,
    data.pre_epsilon_bound,
    data.coefficient_le_epsilon_coefficient,
    data.preliminary_for_move_left⟩

end IUTStage1IUTIVCorollary22HBoundToMoveLeftShadow

/--
The denominator `1 - (2/5) * epsilon_E` appearing in the last absorption step
of the proof of IUT IV, Corollary 2.2(ii).
-/
noncomputable def iutIVCorollary22EpsilonDenominator (epsilonE : Real) : Real :=
  1 - (2 / 5 : Real) * epsilonE

/-- The coefficient of the tripodal log-degree sum before the final absorption. -/
noncomputable def iutIVCorollary22EpsilonMainCoefficient (epsilonE : Real) :
    Real :=
  (iutIVCorollary22EpsilonDenominator epsilonE)⁻¹ *
    (1 + (1 / 5 : Real) * epsilonE)

/-- The coefficient of the constant term before the final absorption. -/
noncomputable def iutIVCorollary22EpsilonConstantTerm
    (epsilonE cK : Real) : Real :=
  (iutIVCorollary22EpsilonDenominator epsilonE)⁻¹ *
    ((1 / 2 : Real) * cK)

/--
IUT IV, Corollary 2.2(ii), moving the `epsilon_E` multiple of `(1/6)h`
to the left-hand side.

This is the algebraic step immediately before the final absorption estimates.
-/
structure IUTStage1IUTIVCorollary22EpsilonMoveLeftShadow where
  h : Real
  logDegreeSum : Real
  cK : Real
  epsilonE : Real
  denominator_pos :
    0 < iutIVCorollary22EpsilonDenominator epsilonE
  preliminary_bound :
    (1 / 6 : Real) * h <=
      (1 + (1 / 5 : Real) * epsilonE) * logDegreeSum +
        (1 / 6 : Real) * h * ((2 / 5 : Real) * epsilonE) +
          (1 / 2 : Real) * cK

namespace IUTStage1IUTIVCorollary22EpsilonMoveLeftShadow

theorem moved_left_bound
    (data : IUTStage1IUTIVCorollary22EpsilonMoveLeftShadow) :
    (1 / 6 : Real) * data.h <=
      iutIVCorollary22EpsilonMainCoefficient data.epsilonE *
          data.logDegreeSum +
        iutIVCorollary22EpsilonConstantTerm data.epsilonE data.cK := by
  let lhs : Real := (1 / 6 : Real) * data.h
  let mainTerm : Real :=
    (1 + (1 / 5 : Real) * data.epsilonE) * data.logDegreeSum
  let constTerm : Real := (1 / 2 : Real) * data.cK
  have hpre :
      lhs <= mainTerm + lhs * ((2 / 5 : Real) * data.epsilonE) + constTerm := by
    dsimp [lhs, mainTerm, constTerm]
    exact data.preliminary_bound
  have hleft :
      iutIVCorollary22EpsilonDenominator data.epsilonE * lhs <=
        mainTerm + constTerm := by
    rw [iutIVCorollary22EpsilonDenominator]
    linarith
  have hdiv :
      lhs <= (mainTerm + constTerm) /
        iutIVCorollary22EpsilonDenominator data.epsilonE := by
    rw [le_div_iff₀ data.denominator_pos]
    simpa [mul_comm] using hleft
  calc
    (1 / 6 : Real) * data.h = lhs := rfl
    _ <= (mainTerm + constTerm) /
        iutIVCorollary22EpsilonDenominator data.epsilonE := hdiv
    _ =
      iutIVCorollary22EpsilonMainCoefficient data.epsilonE *
          data.logDegreeSum +
        iutIVCorollary22EpsilonConstantTerm data.epsilonE data.cK := by
        dsimp [mainTerm, constTerm, iutIVCorollary22EpsilonMainCoefficient,
          iutIVCorollary22EpsilonConstantTerm]
        rw [div_eq_mul_inv]
        ring

theorem move_left_endpoint
    (data : IUTStage1IUTIVCorollary22EpsilonMoveLeftShadow) :
    0 < iutIVCorollary22EpsilonDenominator data.epsilonE ∧
      (1 / 6 : Real) * data.h <=
        (1 + (1 / 5 : Real) * data.epsilonE) * data.logDegreeSum +
          (1 / 6 : Real) * data.h * ((2 / 5 : Real) * data.epsilonE) +
            (1 / 2 : Real) * data.cK ∧
      (1 / 6 : Real) * data.h <=
        iutIVCorollary22EpsilonMainCoefficient data.epsilonE *
            data.logDegreeSum +
          iutIVCorollary22EpsilonConstantTerm data.epsilonE data.cK :=
  ⟨data.denominator_pos,
    data.preliminary_bound,
    data.moved_left_bound⟩

end IUTStage1IUTIVCorollary22EpsilonMoveLeftShadow

/--
IUT IV, Corollary 2.2(ii), final `epsilon_E` absorption.

The source uses `0 < epsilon_E <= 1` to pass from the intermediate inequality
with denominator `(1 - (2/5)epsilon_E)` to the displayed C2 bound.
-/
structure IUTStage1IUTIVCorollary22EpsilonAbsorptionShadow where
  h : Real
  logDegreeSum : Real
  cK : Real
  epsilonE : Real
  epsilonE_pos : 0 < epsilonE
  epsilonE_le_one : epsilonE <= 1
  logDegreeSum_nonneg : 0 <= logDegreeSum
  cK_nonneg : 0 <= cK
  preliminary_bound :
    (1 / 6 : Real) * h <=
      iutIVCorollary22EpsilonMainCoefficient epsilonE * logDegreeSum +
        iutIVCorollary22EpsilonConstantTerm epsilonE cK

namespace IUTStage1IUTIVCorollary22EpsilonAbsorptionShadow

theorem denominator_pos
    (data : IUTStage1IUTIVCorollary22EpsilonAbsorptionShadow) :
    0 < iutIVCorollary22EpsilonDenominator data.epsilonE := by
  rw [iutIVCorollary22EpsilonDenominator]
  nlinarith [data.epsilonE_pos, data.epsilonE_le_one]

theorem denominator_ge_half
    (data : IUTStage1IUTIVCorollary22EpsilonAbsorptionShadow) :
    (1 / 2 : Real) <=
      iutIVCorollary22EpsilonDenominator data.epsilonE := by
  rw [iutIVCorollary22EpsilonDenominator]
  nlinarith [data.epsilonE_le_one]

theorem mainCoefficient_le_one_add_epsilon
    (data : IUTStage1IUTIVCorollary22EpsilonAbsorptionShadow) :
    iutIVCorollary22EpsilonMainCoefficient data.epsilonE <=
      1 + data.epsilonE := by
  have hden := data.denominator_pos
  rw [iutIVCorollary22EpsilonMainCoefficient]
  have hdiv :
      (iutIVCorollary22EpsilonDenominator data.epsilonE)⁻¹ *
          (1 + (1 / 5 : Real) * data.epsilonE) =
        (1 + (1 / 5 : Real) * data.epsilonE) /
          iutIVCorollary22EpsilonDenominator data.epsilonE := by
    rw [div_eq_mul_inv]
    ring
  rw [hdiv, div_le_iff₀ hden]
  rw [iutIVCorollary22EpsilonDenominator]
  have hprod : 0 <= data.epsilonE * (1 - data.epsilonE) :=
    mul_nonneg data.epsilonE_pos.le (sub_nonneg.mpr data.epsilonE_le_one)
  nlinarith

theorem constantTerm_le_cK
    (data : IUTStage1IUTIVCorollary22EpsilonAbsorptionShadow) :
    iutIVCorollary22EpsilonConstantTerm data.epsilonE data.cK <= data.cK := by
  have hden := data.denominator_pos
  have hhalf := data.denominator_ge_half
  have hinv_le_two :
      (iutIVCorollary22EpsilonDenominator data.epsilonE)⁻¹ <=
        (2 : Real) := by
    rw [inv_le_comm₀ hden (by norm_num : (0 : Real) < 2)]
    nlinarith
  have hcoeff :
      (iutIVCorollary22EpsilonDenominator data.epsilonE)⁻¹ *
          (1 / 2 : Real) <= 1 := by
    nlinarith
  rw [iutIVCorollary22EpsilonConstantTerm]
  calc
    (iutIVCorollary22EpsilonDenominator data.epsilonE)⁻¹ *
        ((1 / 2 : Real) * data.cK)
        =
      ((iutIVCorollary22EpsilonDenominator data.epsilonE)⁻¹ *
        (1 / 2 : Real)) * data.cK := by
          ring
    _ <= 1 * data.cK :=
      mul_le_mul_of_nonneg_right hcoeff data.cK_nonneg
    _ = data.cK := by ring

theorem final_bound
    (data : IUTStage1IUTIVCorollary22EpsilonAbsorptionShadow) :
    (1 / 6 : Real) * data.h <=
      (1 + data.epsilonE) * data.logDegreeSum + data.cK := by
  have hmain := data.mainCoefficient_le_one_add_epsilon
  have hmain_mul :
      iutIVCorollary22EpsilonMainCoefficient data.epsilonE *
          data.logDegreeSum <=
        (1 + data.epsilonE) * data.logDegreeSum :=
    mul_le_mul_of_nonneg_right hmain data.logDegreeSum_nonneg
  have hconst := data.constantTerm_le_cK
  calc
    (1 / 6 : Real) * data.h <=
      iutIVCorollary22EpsilonMainCoefficient data.epsilonE *
          data.logDegreeSum +
        iutIVCorollary22EpsilonConstantTerm data.epsilonE data.cK :=
          data.preliminary_bound
    _ <= (1 + data.epsilonE) * data.logDegreeSum + data.cK :=
          add_le_add hmain_mul hconst

theorem epsilon_absorption_endpoint
    (data : IUTStage1IUTIVCorollary22EpsilonAbsorptionShadow) :
    0 < data.epsilonE ∧
      data.epsilonE <= 1 ∧
      0 <= data.logDegreeSum ∧
      0 <= data.cK ∧
      0 < iutIVCorollary22EpsilonDenominator data.epsilonE ∧
      (1 / 2 : Real) <=
        iutIVCorollary22EpsilonDenominator data.epsilonE ∧
      iutIVCorollary22EpsilonMainCoefficient data.epsilonE <=
        1 + data.epsilonE ∧
      iutIVCorollary22EpsilonConstantTerm data.epsilonE data.cK <=
        data.cK ∧
      (1 / 6 : Real) * data.h <=
        iutIVCorollary22EpsilonMainCoefficient data.epsilonE *
            data.logDegreeSum +
          iutIVCorollary22EpsilonConstantTerm data.epsilonE data.cK ∧
      (1 / 6 : Real) * data.h <=
        (1 + data.epsilonE) * data.logDegreeSum + data.cK :=
  ⟨data.epsilonE_pos,
    data.epsilonE_le_one,
    data.logDegreeSum_nonneg,
    data.cK_nonneg,
    data.denominator_pos,
    data.denominator_ge_half,
    data.mainCoefficient_le_one_add_epsilon,
    data.constantTerm_le_cK,
    data.preliminary_bound,
    data.final_bound⟩

end IUTStage1IUTIVCorollary22EpsilonAbsorptionShadow

/--
IUT IV, Corollary 2.2(ii), final `h = log(q_all)` bound.

This record composes the pre-`epsilon_E` bound, the definition of
`epsilon_E`, the move-left denominator step, and the final absorption estimates.
-/
structure IUTStage1IUTIVCorollary22FinalHBoundShadow where
  h : Real
  logDegreeSum : Real
  cK : Real
  delta : Real
  sqrtH : Real
  logTwoDeltaH : Real
  epsilonE : Real
  sqrtH_pos : 0 < sqrtH
  delta_sq_log_nonneg : 0 <= delta ^ 2 * logTwoDeltaH
  h_eq_sqrtH_sq : h = sqrtH ^ 2
  epsilonE_eq :
    epsilonE =
      iutIVCorollary22EpsilonDefinitionRHS delta sqrtH logTwoDeltaH
  logDegreeSum_nonneg : 0 <= logDegreeSum
  delta_inv_sqrtH_le_epsilon_over_five :
    delta / sqrtH <= (1 / 5 : Real) * epsilonE
  epsilonE_pos : 0 < epsilonE
  epsilonE_le_one : epsilonE <= 1
  cK_nonneg : 0 <= cK
  pre_epsilon_bound :
    (1 / 6 : Real) * h <=
      (1 + delta / sqrtH) * logDegreeSum +
        (15 * delta) ^ 2 * sqrtH * logTwoDeltaH +
          (1 / 2 : Real) * cK

namespace IUTStage1IUTIVCorollary22FinalHBoundShadow

def errorConversion
    (data : IUTStage1IUTIVCorollary22FinalHBoundShadow) :
    IUTStage1IUTIVCorollary22EpsilonErrorConversionShadow :=
  { h := data.h
    delta := data.delta
    sqrtH := data.sqrtH
    logTwoDeltaH := data.logTwoDeltaH
    epsilonE := data.epsilonE
    sqrtH_pos := data.sqrtH_pos
    delta_sq_log_nonneg := data.delta_sq_log_nonneg
    h_eq_sqrtH_sq := data.h_eq_sqrtH_sq
    epsilonE_eq := data.epsilonE_eq }

def hBoundToMoveLeft
    (data : IUTStage1IUTIVCorollary22FinalHBoundShadow) :
    IUTStage1IUTIVCorollary22HBoundToMoveLeftShadow :=
  { h := data.h
    logDegreeSum := data.logDegreeSum
    cK := data.cK
    delta := data.delta
    sqrtH := data.sqrtH
    logTwoDeltaH := data.logTwoDeltaH
    epsilonE := data.epsilonE
    logDegreeSum_nonneg := data.logDegreeSum_nonneg
    delta_inv_sqrtH_le_epsilon_over_five :=
      data.delta_inv_sqrtH_le_epsilon_over_five
    error_conversion_bound :=
      data.errorConversion.fifteen_delta_sq_error_le_epsilon_term
    pre_epsilon_bound := data.pre_epsilon_bound }

def moveLeft
    (data : IUTStage1IUTIVCorollary22FinalHBoundShadow) :
    IUTStage1IUTIVCorollary22EpsilonMoveLeftShadow :=
  { h := data.h
    logDegreeSum := data.logDegreeSum
    cK := data.cK
    epsilonE := data.epsilonE
    denominator_pos := by
      rw [iutIVCorollary22EpsilonDenominator]
      nlinarith [data.epsilonE_pos, data.epsilonE_le_one]
    preliminary_bound := data.hBoundToMoveLeft.preliminary_for_move_left }

def absorption
    (data : IUTStage1IUTIVCorollary22FinalHBoundShadow) :
    IUTStage1IUTIVCorollary22EpsilonAbsorptionShadow :=
  { h := data.h
    logDegreeSum := data.logDegreeSum
    cK := data.cK
    epsilonE := data.epsilonE
    epsilonE_pos := data.epsilonE_pos
    epsilonE_le_one := data.epsilonE_le_one
    logDegreeSum_nonneg := data.logDegreeSum_nonneg
    cK_nonneg := data.cK_nonneg
    preliminary_bound := data.moveLeft.moved_left_bound }

theorem final_h_bound
    (data : IUTStage1IUTIVCorollary22FinalHBoundShadow) :
    (1 / 6 : Real) * data.h <=
      (1 + data.epsilonE) * data.logDegreeSum + data.cK :=
  data.absorption.final_bound

theorem final_h_bound_endpoint
    (data : IUTStage1IUTIVCorollary22FinalHBoundShadow) :
    0 < data.sqrtH ∧
      0 <= data.delta ^ 2 * data.logTwoDeltaH ∧
      data.h = data.sqrtH ^ 2 ∧
      data.epsilonE =
        iutIVCorollary22EpsilonDefinitionRHS
          data.delta data.sqrtH data.logTwoDeltaH ∧
      0 <= data.logDegreeSum ∧
      data.delta / data.sqrtH <= (1 / 5 : Real) * data.epsilonE ∧
      0 < data.epsilonE ∧
      data.epsilonE <= 1 ∧
      0 <= data.cK ∧
      (1 / 6 : Real) * data.h <=
        (1 + data.delta / data.sqrtH) * data.logDegreeSum +
          (15 * data.delta) ^ 2 * data.sqrtH * data.logTwoDeltaH +
            (1 / 2 : Real) * data.cK ∧
      (1 / 6 : Real) * data.h <=
        (1 + data.epsilonE) * data.logDegreeSum + data.cK :=
  ⟨data.sqrtH_pos,
    data.delta_sq_log_nonneg,
    data.h_eq_sqrtH_sq,
    data.epsilonE_eq,
    data.logDegreeSum_nonneg,
    data.delta_inv_sqrtH_le_epsilon_over_five,
    data.epsilonE_pos,
    data.epsilonE_le_one,
    data.cK_nonneg,
    data.pre_epsilon_bound,
    data.final_h_bound⟩

end IUTStage1IUTIVCorollary22FinalHBoundShadow

/--
IUT IV, Corollary 2.2(ii), comparison of curve functions with tripodal field
terms.

The source records the tautological equality
`log-diff_X(x_E) = log(d_Ftpd)` and the inequalities
`log(f_Ftpd) <= log-cond_D(x_E) <= log(f_Ftpd) + log(2l)`.
-/
structure IUTStage1IUTIVCorollary22LogDiffCondComparisonShadow where
  logDiffX : Real
  logCondD : Real
  logDifferentFtpd : Real
  logConductorFtpd : Real
  logTwoL : Real
  logDiff_eq_logDifferentFtpd :
    logDiffX = logDifferentFtpd
  logConductorFtpd_le_logCondD :
    logConductorFtpd <= logCondD
  logCondD_le_logConductorFtpd_add_logTwoL :
    logCondD <= logConductorFtpd + logTwoL

namespace IUTStage1IUTIVCorollary22LogDiffCondComparisonShadow

def curveLogSum
    (data : IUTStage1IUTIVCorollary22LogDiffCondComparisonShadow) : Real :=
  data.logDiffX + data.logCondD

def ftpdLogSum
    (data : IUTStage1IUTIVCorollary22LogDiffCondComparisonShadow) : Real :=
  data.logDifferentFtpd + data.logConductorFtpd

theorem ftpdLogSum_le_curveLogSum
    (data : IUTStage1IUTIVCorollary22LogDiffCondComparisonShadow) :
    data.ftpdLogSum <= data.curveLogSum := by
  dsimp [ftpdLogSum, curveLogSum]
  rw [data.logDiff_eq_logDifferentFtpd]
  linarith [data.logConductorFtpd_le_logCondD]

theorem curveLogSum_le_ftpdLogSum_add_logTwoL
    (data : IUTStage1IUTIVCorollary22LogDiffCondComparisonShadow) :
    data.curveLogSum <= data.ftpdLogSum + data.logTwoL := by
  dsimp [ftpdLogSum, curveLogSum]
  rw [data.logDiff_eq_logDifferentFtpd]
  linarith [data.logCondD_le_logConductorFtpd_add_logTwoL]

theorem logDiffCondComparison_endpoint
    (data : IUTStage1IUTIVCorollary22LogDiffCondComparisonShadow) :
    data.logDiffX = data.logDifferentFtpd ∧
      data.logConductorFtpd <= data.logCondD ∧
      data.logCondD <= data.logConductorFtpd + data.logTwoL ∧
      data.ftpdLogSum <= data.curveLogSum ∧
      data.curveLogSum <= data.ftpdLogSum + data.logTwoL :=
  ⟨data.logDiff_eq_logDifferentFtpd,
    data.logConductorFtpd_le_logCondD,
    data.logCondD_le_logConductorFtpd_add_logTwoL,
    data.ftpdLogSum_le_curveLogSum,
    data.curveLogSum_le_ftpdLogSum_add_logTwoL⟩

end IUTStage1IUTIVCorollary22LogDiffCondComparisonShadow

/--
IUT IV, Corollary 2.2(ii), final passage from the `h = log(q_all)` bound to
condition (C2).

The source uses the comparison of tripodal different/conductor terms with
`log-diff_X(x_E) + log-cond_D(x_E)` to turn the final `h` bound into the
displayed C2 inequality chain.
-/
structure IUTStage1IUTIVCorollary22FinalHToC2Shadow where
  logQ : Real
  logQTwo : Real
  logQAll : Real
  h : Real
  epsilonE : Real
  logDegreeSum : Real
  logDiffX : Real
  logCondD : Real
  cK : Real
  h_eq_logQAll : h = logQAll
  epsilonE_pos : 0 < epsilonE
  logDegreeSum_le_curveSum :
    logDegreeSum <= logDiffX + logCondD
  final_h_bound :
    (1 / 6 : Real) * h <=
      (1 + epsilonE) * logDegreeSum + cK
  logQ_le_logQTwo :
    (1 / 6 : Real) * logQ <= (1 / 6 : Real) * logQTwo
  logQTwo_le_logQAll :
    (1 / 6 : Real) * logQTwo <= (1 / 6 : Real) * logQAll

namespace IUTStage1IUTIVCorollary22FinalHToC2Shadow

theorem one_plus_epsilonE_nonneg
    (data : IUTStage1IUTIVCorollary22FinalHToC2Shadow) :
    0 <= 1 + data.epsilonE := by
  linarith [data.epsilonE_pos]

theorem logQAll_le_curveSide
    (data : IUTStage1IUTIVCorollary22FinalHToC2Shadow) :
    (1 / 6 : Real) * data.logQAll <=
      (1 + data.epsilonE) * (data.logDiffX + data.logCondD) + data.cK := by
  have hmono :
      (1 + data.epsilonE) * data.logDegreeSum <=
        (1 + data.epsilonE) * (data.logDiffX + data.logCondD) :=
    mul_le_mul_of_nonneg_left data.logDegreeSum_le_curveSum
      data.one_plus_epsilonE_nonneg
  calc
    (1 / 6 : Real) * data.logQAll =
        (1 / 6 : Real) * data.h := by rw [data.h_eq_logQAll]
    _ <= (1 + data.epsilonE) * data.logDegreeSum + data.cK :=
        data.final_h_bound
    _ <= (1 + data.epsilonE) * (data.logDiffX + data.logCondD) + data.cK :=
        add_le_add hmono le_rfl

def toC2InequalityChain
    (data : IUTStage1IUTIVCorollary22FinalHToC2Shadow) :
    IUTStage1IUTIVCorollary22C2InequalityChainShadow :=
  { logQ := data.logQ
    logQTwo := data.logQTwo
    logQAll := data.logQAll
    epsilonE := data.epsilonE
    logDiffX := data.logDiffX
    logCondD := data.logCondD
    cK := data.cK
    logQ_le_logQTwo := data.logQ_le_logQTwo
    logQTwo_le_logQAll := data.logQTwo_le_logQAll
    logQAll_le_heightSide := data.logQAll_le_curveSide }

theorem final_h_to_c2_endpoint
    (data : IUTStage1IUTIVCorollary22FinalHToC2Shadow) :
    data.h = data.logQAll ∧
      0 < data.epsilonE ∧
      0 <= 1 + data.epsilonE ∧
      data.logDegreeSum <= data.logDiffX + data.logCondD ∧
      (1 / 6 : Real) * data.h <=
        (1 + data.epsilonE) * data.logDegreeSum + data.cK ∧
      (1 / 6 : Real) * data.logQ <=
        (1 / 6 : Real) * data.logQTwo ∧
      (1 / 6 : Real) * data.logQTwo <=
        (1 / 6 : Real) * data.logQAll ∧
      (1 / 6 : Real) * data.logQAll <=
        (1 + data.epsilonE) * (data.logDiffX + data.logCondD) + data.cK ∧
      (1 / 6 : Real) * data.logQ <= data.toC2InequalityChain.heightSide ∧
      (1 / 6 : Real) * data.logQTwo <= data.toC2InequalityChain.heightSide :=
  ⟨data.h_eq_logQAll,
    data.epsilonE_pos,
    data.one_plus_epsilonE_nonneg,
    data.logDegreeSum_le_curveSum,
    data.final_h_bound,
    data.logQ_le_logQTwo,
    data.logQTwo_le_logQAll,
    data.logQAll_le_curveSide,
    data.toC2InequalityChain.logQ_le_heightSide,
    data.toC2InequalityChain.logQTwo_le_heightSide⟩

end IUTStage1IUTIVCorollary22FinalHToC2Shadow

/--
IUT IV, Corollary 2.2 to Theorem A bounded-discrepancy passage.

Corollary 2.2(i) compares `(1/6)log(q_2)` with the canonical height up to
bounded discrepancy; Corollary 2.2(ii)(C2) bounds `(1/6)log(q_2)` by the
different/conductor side.  This record proves the resulting lower bound for
`(1 + epsilon_E) * (log-diff + log-cond) - height`.
-/
structure IUTStage1IUTIVCorollary22ToTheoremABoundShadow
    (Point : Type u) where
  epsilonE : Real
  cK : Real
  logQTwo : Point -> Real
  canonicalHeight : Point -> Real
  logDiff : Point -> Real
  logCond : Point -> Real
  logQTwo_to_canonicalHeight :
    IUTStage1BoundedDiscrepancyEquivalent Point
      (fun x => (1 / 6 : Real) * logQTwo x)
      canonicalHeight
  c2_logQTwo_bound :
    ∀ x : Point,
      (1 / 6 : Real) * logQTwo x <=
        (1 + epsilonE) * (logDiff x + logCond x) + cK

namespace IUTStage1IUTIVCorollary22ToTheoremABoundShadow

variable {Point : Type u}

def lowerBound
    (data : IUTStage1IUTIVCorollary22ToTheoremABoundShadow Point) :
    Real :=
  data.logQTwo_to_canonicalHeight.lower - data.cK

def discrepancy
    (data : IUTStage1IUTIVCorollary22ToTheoremABoundShadow Point)
    (x : Point) : Real :=
  (1 + data.epsilonE) * (data.logDiff x + data.logCond x) -
    data.canonicalHeight x

theorem canonicalHeight_le_weightedSide_minus_lower
    (data : IUTStage1IUTIVCorollary22ToTheoremABoundShadow Point)
    (x : Point) :
    data.canonicalHeight x <=
      (1 + data.epsilonE) * (data.logDiff x + data.logCond x) +
        data.cK - data.logQTwo_to_canonicalHeight.lower := by
  have hbd := data.logQTwo_to_canonicalHeight.lower_bound x
  have hc2 := data.c2_logQTwo_bound x
  linarith

theorem discrepancy_bounded_below
    (data : IUTStage1IUTIVCorollary22ToTheoremABoundShadow Point)
    (x : Point) :
    data.lowerBound <= data.discrepancy x := by
  have hheight := data.canonicalHeight_le_weightedSide_minus_lower x
  dsimp [lowerBound, discrepancy]
  linarith

theorem theoremA_handoff_endpoint
    (data : IUTStage1IUTIVCorollary22ToTheoremABoundShadow Point)
    (x : Point) :
    data.logQTwo_to_canonicalHeight.lower <=
        (1 / 6 : Real) * data.logQTwo x - data.canonicalHeight x ∧
      (1 / 6 : Real) * data.logQTwo x <=
        (1 + data.epsilonE) * (data.logDiff x + data.logCond x) +
          data.cK ∧
      data.canonicalHeight x <=
        (1 + data.epsilonE) * (data.logDiff x + data.logCond x) +
          data.cK - data.logQTwo_to_canonicalHeight.lower ∧
      data.lowerBound <= data.discrepancy x :=
  ⟨data.logQTwo_to_canonicalHeight.lower_bound x,
    data.c2_logQTwo_bound x,
    data.canonicalHeight_le_weightedSide_minus_lower x,
    data.discrepancy_bounded_below x⟩

noncomputable def toTheoremABoundedDiscrepancyShadow
    (data : IUTStage1IUTIVCorollary22ToTheoremABoundShadow Point)
    (d : Nat) (d_pos : 0 < d)
    (epsilonE_pos : 0 < data.epsilonE)
    (hyperbolicCurve : Prop) (hyperbolic_curve : hyperbolicCurve) :
    IUTStage1IUTIVTheoremABoundedDiscrepancyShadow Point :=
  { d := d
    d_pos := d_pos
    epsilon := data.epsilonE
    epsilon_pos := epsilonE_pos
    hyperbolicCurve := hyperbolicCurve
    hyperbolic_curve := hyperbolic_curve
    height := data.canonicalHeight
    logDiff := data.logDiff
    logCond := data.logCond
    lowerBound := data.lowerBound
    discrepancy_bounded_below := data.discrepancy_bounded_below }

end IUTStage1IUTIVCorollary22ToTheoremABoundShadow

/--
Finite-exception lower-bound gluing.

Corollary 2.2(ii),(iii) repeatedly enlarges finite exceptional sets.  At the
real-valued inequality level, the bookkeeping principle is that a lower bound on
the complement of a finite exceptional set, together with a lower bound on the
exceptional set itself, gives a global lower bound by taking the minimum of the
two constants.
-/
structure IUTStage1FiniteExceptionLowerBoundShadow
    (Point : Type u) [DecidableEq Point] where
  exceptional : Finset Point
  function : Point -> Real
  genericLowerBound : Real
  exceptionalLowerBound : Real
  generic_bound :
    ∀ x : Point, x ∉ exceptional -> genericLowerBound <= function x
  exceptional_bound :
    ∀ x : Point, x ∈ exceptional -> exceptionalLowerBound <= function x

namespace IUTStage1FiniteExceptionLowerBoundShadow

variable {Point : Type u} [DecidableEq Point]

noncomputable def globalLowerBound
    (data : IUTStage1FiniteExceptionLowerBoundShadow Point) : Real :=
  min data.genericLowerBound data.exceptionalLowerBound

theorem globalLowerBound_le_genericLowerBound
    (data : IUTStage1FiniteExceptionLowerBoundShadow Point) :
    data.globalLowerBound <= data.genericLowerBound :=
  min_le_left data.genericLowerBound data.exceptionalLowerBound

theorem globalLowerBound_le_exceptionalLowerBound
    (data : IUTStage1FiniteExceptionLowerBoundShadow Point) :
    data.globalLowerBound <= data.exceptionalLowerBound :=
  min_le_right data.genericLowerBound data.exceptionalLowerBound

theorem global_bound
    (data : IUTStage1FiniteExceptionLowerBoundShadow Point)
    (x : Point) :
    data.globalLowerBound <= data.function x := by
  by_cases hx : x ∈ data.exceptional
  · exact le_trans data.globalLowerBound_le_exceptionalLowerBound
      (data.exceptional_bound x hx)
  · exact le_trans data.globalLowerBound_le_genericLowerBound
      (data.generic_bound x hx)

theorem finite_exception_endpoint
    (data : IUTStage1FiniteExceptionLowerBoundShadow Point)
    (x : Point) :
    data.globalLowerBound <= data.genericLowerBound ∧
      data.globalLowerBound <= data.exceptionalLowerBound ∧
      data.globalLowerBound <= data.function x :=
  ⟨data.globalLowerBound_le_genericLowerBound,
    data.globalLowerBound_le_exceptionalLowerBound,
    data.global_bound x⟩

end IUTStage1FiniteExceptionLowerBoundShadow

/--
IUT IV, Corollary 2.2 exceptional-set passage toward Corollary 2.3.

This packages finite-exception gluing for the specific
height/different/conductor discrepancy that appears in Theorem A and
Corollary 2.3.
-/
structure IUTStage1IUTIVCorollary22FiniteExceptionTheoremAShadow
    (Point : Type u) [DecidableEq Point] where
  exceptional : Finset Point
  epsilon : Real
  height : Point -> Real
  logDiff : Point -> Real
  logCond : Point -> Real
  genericLowerBound : Real
  exceptionalLowerBound : Real
  generic_bound :
    ∀ x : Point, x ∉ exceptional ->
      genericLowerBound <=
        (1 + epsilon) * (logDiff x + logCond x) - height x
  exceptional_bound :
    ∀ x : Point, x ∈ exceptional ->
      exceptionalLowerBound <=
        (1 + epsilon) * (logDiff x + logCond x) - height x

namespace IUTStage1IUTIVCorollary22FiniteExceptionTheoremAShadow

variable {Point : Type u} [DecidableEq Point]

def discrepancy
    (data : IUTStage1IUTIVCorollary22FiniteExceptionTheoremAShadow Point)
    (x : Point) : Real :=
  (1 + data.epsilon) * (data.logDiff x + data.logCond x) - data.height x

def toFiniteExceptionLowerBound
    (data : IUTStage1IUTIVCorollary22FiniteExceptionTheoremAShadow Point) :
    IUTStage1FiniteExceptionLowerBoundShadow Point :=
  { exceptional := data.exceptional
    function := data.discrepancy
    genericLowerBound := data.genericLowerBound
    exceptionalLowerBound := data.exceptionalLowerBound
    generic_bound := data.generic_bound
    exceptional_bound := data.exceptional_bound }

noncomputable def globalLowerBound
    (data : IUTStage1IUTIVCorollary22FiniteExceptionTheoremAShadow Point) :
    Real :=
  data.toFiniteExceptionLowerBound.globalLowerBound

theorem discrepancy_bounded_below
    (data : IUTStage1IUTIVCorollary22FiniteExceptionTheoremAShadow Point)
    (x : Point) :
    data.globalLowerBound <= data.discrepancy x :=
  data.toFiniteExceptionLowerBound.global_bound x

theorem finite_exception_theoremA_endpoint
    (data : IUTStage1IUTIVCorollary22FiniteExceptionTheoremAShadow Point)
    (x : Point) :
    data.globalLowerBound <= data.genericLowerBound ∧
      data.globalLowerBound <= data.exceptionalLowerBound ∧
      data.globalLowerBound <= data.discrepancy x :=
  ⟨data.toFiniteExceptionLowerBound.globalLowerBound_le_genericLowerBound,
    data.toFiniteExceptionLowerBound.globalLowerBound_le_exceptionalLowerBound,
    data.discrepancy_bounded_below x⟩

end IUTStage1IUTIVCorollary22FiniteExceptionTheoremAShadow

/--
IUT IV, Corollary 2.3 Diophantine inequality shadow.

The source proof reduces the general hyperbolic curve statement to the
projective-line/three-point compact-subset statement by invoking [GenEll],
Theorem 2.1.  This record does not formalize GenEll; it keeps the exact
real-valued consequence of that reduction as an explicit transfer hypothesis.
-/
structure IUTStage1IUTIVCorollary23DiophantineInequalityShadow
    (Point : Type u) where
  d : Nat
  d_pos : 0 < d
  epsilon : Real
  epsilon_pos : 0 < epsilon
  hyperbolicCurve : Prop
  hyperbolic_curve : hyperbolicCurve
  height : Point -> Real
  logDiff : Point -> Real
  logCond : Point -> Real
  compactSubsetTheoremA : Prop
  compact_subset_theoremA : compactSubsetTheoremA
  genEll_transfer :
    compactSubsetTheoremA ->
      ∃ lowerBound : Real,
        ∀ x : Point,
          lowerBound <=
            (1 + epsilon) * (logDiff x + logCond x) - height x

namespace IUTStage1IUTIVCorollary23DiophantineInequalityShadow

variable {Point : Type u}

def discrepancy
    (data : IUTStage1IUTIVCorollary23DiophantineInequalityShadow Point)
    (x : Point) : Real :=
  (1 + data.epsilon) * (data.logDiff x + data.logCond x) - data.height x

theorem exists_lowerBound
    (data : IUTStage1IUTIVCorollary23DiophantineInequalityShadow Point) :
    ∃ lowerBound : Real, ∀ x : Point, lowerBound <= data.discrepancy x := by
  rcases data.genEll_transfer data.compact_subset_theoremA with
    ⟨lowerBound, hbound⟩
  exact ⟨lowerBound, hbound⟩

noncomputable def lowerBound
    (data : IUTStage1IUTIVCorollary23DiophantineInequalityShadow Point) :
    Real :=
  Classical.choose data.exists_lowerBound

theorem discrepancy_bounded_below
    (data : IUTStage1IUTIVCorollary23DiophantineInequalityShadow Point)
    (x : Point) :
    data.lowerBound <= data.discrepancy x :=
  Classical.choose_spec data.exists_lowerBound x

theorem diophantine_inequality_endpoint
    (data : IUTStage1IUTIVCorollary23DiophantineInequalityShadow Point)
    (x : Point) :
    0 < data.d ∧
      0 < data.epsilon ∧
      data.hyperbolicCurve ∧
      data.compactSubsetTheoremA ∧
      (∃ lowerBound : Real, ∀ y : Point, lowerBound <= data.discrepancy y) ∧
      data.lowerBound <= data.discrepancy x :=
  ⟨data.d_pos,
    data.epsilon_pos,
    data.hyperbolic_curve,
    data.compact_subset_theoremA,
    data.exists_lowerBound,
    data.discrepancy_bounded_below x⟩

noncomputable def toTheoremABoundedDiscrepancyShadow
    (data : IUTStage1IUTIVCorollary23DiophantineInequalityShadow Point) :
    IUTStage1IUTIVTheoremABoundedDiscrepancyShadow Point :=
  { d := data.d
    d_pos := data.d_pos
    epsilon := data.epsilon
    epsilon_pos := data.epsilon_pos
    hyperbolicCurve := data.hyperbolicCurve
    hyperbolic_curve := data.hyperbolic_curve
    height := data.height
    logDiff := data.logDiff
    logCond := data.logCond
    lowerBound := data.lowerBound
    discrepancy_bounded_below := data.discrepancy_bounded_below }

end IUTStage1IUTIVCorollary23DiophantineInequalityShadow
end Stage1
end Iut
