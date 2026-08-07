/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Foundations.Geometry.TateCurveDiscriminantEstimates
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateLocalCarrier

/-!
# Local reduction of the canonical p-adic Tate equation

For a prime `p >= 5`, the canonical q-series equation at `q = p` has an
explicit integral equation over `Z_p`.  The preceding estimate modules prove
that its integral `c4` is a unit and that its integral discriminant belongs to
the maximal ideal while remaining nonzero on the generic fibre.  This module
uses precisely those facts to prove minimality, multiplicative reduction, and
split multiplicative reduction.

The reduced equation is identified with

`y^2 + x*y = x^3`.

Its tangent polynomial is proved equal to `T * (T + 1)`, and a direct
normalization calculation exhibits the two parameters `0` and `-1` above the
node.  These are properties of the canonical local q-series equation.  No
identification with a separately supplied number-field elliptic curve and no
Tate analytic uniformization theorem is asserted here.
-/

namespace LeanFormal.IUT

open Polynomial

noncomputable section

namespace TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

abbrev ResidueField : Type := IsLocalRing.ResidueField ℤ_[l.value]

section IntegralModel

theorem integralCurve_c4_cast :
    algebraMap ℤ_[l.value] ℚ_[l.value] (integralCurve l).c₄ =
      (canonicalCurve l).c₄ := by
  have h := congrArg (fun W : WeierstrassCurve ℚ_[l.value] => W.c₄)
    (integralCurveMap_eq_canonical l)
  simpa [integralCurveMap, WeierstrassCurve.map_c₄] using h

theorem integralCurve_c6_cast :
    algebraMap ℤ_[l.value] ℚ_[l.value] (integralCurve l).c₆ =
      (canonicalCurve l).c₆ := by
  have h := congrArg (fun W : WeierstrassCurve ℚ_[l.value] => W.c₆)
    (integralCurveMap_eq_canonical l)
  simpa [integralCurveMap, WeierstrassCurve.map_c₆] using h

theorem integralCurve_b2_cast :
    algebraMap ℤ_[l.value] ℚ_[l.value] (integralCurve l).b₂ =
      (canonicalCurve l).b₂ := by
  have h := congrArg (fun W : WeierstrassCurve ℚ_[l.value] => W.b₂)
    (integralCurveMap_eq_canonical l)
  simpa [integralCurveMap, WeierstrassCurve.map_b₂] using h

theorem integralCurve_b4_cast :
    algebraMap ℤ_[l.value] ℚ_[l.value] (integralCurve l).b₄ =
      (canonicalCurve l).b₄ := by
  have h := congrArg (fun W : WeierstrassCurve ℚ_[l.value] => W.b₄)
    (integralCurveMap_eq_canonical l)
  simpa [integralCurveMap, WeierstrassCurve.map_b₄] using h

theorem integralCurve_b6_cast :
    algebraMap ℤ_[l.value] ℚ_[l.value] (integralCurve l).b₆ =
      (canonicalCurve l).b₆ := by
  have h := congrArg (fun W : WeierstrassCurve ℚ_[l.value] => W.b₆)
    (integralCurveMap_eq_canonical l)
  simpa [integralCurveMap, WeierstrassCurve.map_b₆] using h

theorem integralCurve_b8_cast :
    algebraMap ℤ_[l.value] ℚ_[l.value] (integralCurve l).b₈ =
      (canonicalCurve l).b₈ := by
  have h := congrArg (fun W : WeierstrassCurve ℚ_[l.value] => W.b₈)
    (integralCurveMap_eq_canonical l)
  simpa [integralCurveMap, WeierstrassCurve.map_b₈] using h

theorem canonicalCurve_c4_valuation_eq_one :
    (IsDiscreteValuationRing.maximalIdeal ℤ_[l.value]).valuation
      ℚ_[l.value] (canonicalCurve l).c₄ = 1 := by
  rw [← integralCurve_c4_cast l]
  apply ((IsDiscreteValuationRing.maximalIdeal ℤ_[l.value]).valuation_eq_one_iff_notMem
    (K := ℚ_[l.value])).mpr
  change (integralCurve l).c₄ ∉ IsLocalRing.maximalIdeal ℤ_[l.value]
  exact IsLocalRing.notMem_maximalIdeal.mpr
    (integralPresentation_c4_is_unit l)

theorem canonicalCurve_delta_valuation_lt_one :
    (IsDiscreteValuationRing.maximalIdeal ℤ_[l.value]).valuation
      ℚ_[l.value] (canonicalCurve l).Δ < 1 := by
  rw [← integralCurve_delta_cast_is_canonical l]
  apply ((IsDiscreteValuationRing.maximalIdeal ℤ_[l.value]).valuation_lt_one_iff_mem
    (K := ℚ_[l.value]) (integralCurve l).Δ).mpr
  change (integralCurve l).Δ ∈ IsLocalRing.maximalIdeal ℤ_[l.value]
  exact integralCurveDelta_mem_maximalIdeal l

theorem canonicalCurve_delta_valuation_ne_one :
    (IsDiscreteValuationRing.maximalIdeal ℤ_[l.value]).valuation
      ℚ_[l.value] (canonicalCurve l).Δ ≠ 1 :=
  ne_of_lt (canonicalCurve_delta_valuation_lt_one l)

theorem canonicalCurve_isMinimal :
    WeierstrassCurve.IsMinimal ℤ_[l.value] (canonicalCurve l) := by
  letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
    canonicalCurve_is_integral l
  exact isMinimal_of_isIntegral_valuation_c₄_eq_one
    ℤ_[l.value] (canonicalCurve l) (canonicalCurve_c4_valuation_eq_one l)

theorem canonicalCurve_integralModel_eq_integralCurve :
    letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_is_integral l
    (canonicalCurve l).integralModel ℤ_[l.value] = integralCurve l := by
  letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
    canonicalCurve_is_integral l
  apply WeierstrassCurve.map_injective
    (FaithfulSMul.algebraMap_injective ℤ_[l.value] ℚ_[l.value])
  change
    ((canonicalCurve l).integralModel ℤ_[l.value]).baseChange ℚ_[l.value] =
      (integralCurve l).baseChange ℚ_[l.value]
  rw [WeierstrassCurve.baseChange_integralModel_eq]
  exact (integralCurveMap_eq_canonical l).symm

theorem canonicalCurve_integralModel_a1 :
    letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_is_integral l
    ((canonicalCurve l).integralModel ℤ_[l.value]).a₁ = 1 := by
  rw [canonicalCurve_integralModel_eq_integralCurve l]
  exact integralCurve_a1 l

theorem canonicalCurve_integralModel_a2 :
    letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_is_integral l
    ((canonicalCurve l).integralModel ℤ_[l.value]).a₂ = 0 := by
  rw [canonicalCurve_integralModel_eq_integralCurve l]
  exact integralCurve_a2 l

theorem canonicalCurve_integralModel_a3 :
    letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_is_integral l
    ((canonicalCurve l).integralModel ℤ_[l.value]).a₃ = 0 := by
  rw [canonicalCurve_integralModel_eq_integralCurve l]
  exact integralCurve_a3 l

theorem canonicalCurve_integralModel_a4 :
    letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_is_integral l
    ((canonicalCurve l).integralModel ℤ_[l.value]).a₄ = integralA4 l := by
  rw [canonicalCurve_integralModel_eq_integralCurve l]
  exact integralCurve_a4 l

theorem canonicalCurve_integralModel_a6 :
    letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_is_integral l
    ((canonicalCurve l).integralModel ℤ_[l.value]).a₆ = integralA6 l := by
  rw [canonicalCurve_integralModel_eq_integralCurve l]
  exact integralCurve_a6 l

theorem canonicalCurve_integralModel_c4_isUnit :
    letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_is_integral l
    IsUnit ((canonicalCurve l).integralModel ℤ_[l.value]).c₄ := by
  rw [canonicalCurve_integralModel_eq_integralCurve l]
  exact integralPresentation_c4_is_unit l

theorem canonicalCurve_integralModel_delta_mem_maximalIdeal :
    letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_is_integral l
    ((canonicalCurve l).integralModel ℤ_[l.value]).Δ ∈
      IsLocalRing.maximalIdeal ℤ_[l.value] := by
  rw [canonicalCurve_integralModel_eq_integralCurve l]
  exact integralCurveDelta_mem_maximalIdeal l

theorem canonicalCurve_integralModel_delta_ne_zero :
    letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_is_integral l
    ((canonicalCurve l).integralModel ℤ_[l.value]).Δ ≠ 0 := by
  rw [canonicalCurve_integralModel_eq_integralCurve l]
  exact integralCurveDelta_ne_zero l

end IntegralModel

section ResidueEquation

@[simp] theorem residue_integralA4 :
    IsLocalRing.residue ℤ_[l.value] (integralA4 l) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact integralA4_inMaximalIdeal l

@[simp] theorem residue_integralA6 :
    IsLocalRing.residue ℤ_[l.value] (integralA6 l) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  exact integralA6_inMaximalIdeal l

@[simp] theorem residue_integralCurve_delta :
    IsLocalRing.residue ℤ_[l.value] (integralCurve l).Δ = 0 :=
  integralCurve_delta_residue_zero l

@[simp] theorem residue_integralCurve_c4_ne_zero :
    IsLocalRing.residue ℤ_[l.value] (integralCurve l).c₄ ≠ 0 :=
  integralCurve_c4_residue_ne_zero l

def nodalCurve : WeierstrassCurve (ResidueField l) :=
  WeierstrassCurve.mk 1 0 0 0 0

noncomputable def reducedIntegralCurve : WeierstrassCurve (ResidueField l) :=
  (integralCurve l).map (IsLocalRing.residue ℤ_[l.value])

theorem reducedIntegralCurve_eq_nodalCurve :
    reducedIntegralCurve l = nodalCurve l := by
  ext <;> simp [reducedIntegralCurve, nodalCurve, integralCurve]

@[simp] theorem nodalCurve_a1 : (nodalCurve l).a₁ = 1 := rfl

@[simp] theorem nodalCurve_a2 : (nodalCurve l).a₂ = 0 := rfl

@[simp] theorem nodalCurve_a3 : (nodalCurve l).a₃ = 0 := rfl

@[simp] theorem nodalCurve_a4 : (nodalCurve l).a₄ = 0 := rfl

@[simp] theorem nodalCurve_a6 : (nodalCurve l).a₆ = 0 := rfl

@[simp] theorem nodalCurve_b2 : (nodalCurve l).b₂ = 1 := by
  simp [nodalCurve, WeierstrassCurve.b₂]

@[simp] theorem nodalCurve_b4 : (nodalCurve l).b₄ = 0 := by
  simp [nodalCurve, WeierstrassCurve.b₄]

@[simp] theorem nodalCurve_b6 : (nodalCurve l).b₆ = 0 := by
  simp [nodalCurve, WeierstrassCurve.b₆]

@[simp] theorem nodalCurve_b8 : (nodalCurve l).b₈ = 0 := by
  simp [nodalCurve, WeierstrassCurve.b₈]

@[simp] theorem nodalCurve_c4 : (nodalCurve l).c₄ = 1 := by
  simp [nodalCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]

@[simp] theorem nodalCurve_c6 : (nodalCurve l).c₆ = -1 := by
  simp [nodalCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]

@[simp] theorem nodalCurve_delta : (nodalCurve l).Δ = 0 := by
  simp [nodalCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

@[simp] theorem reducedIntegralCurve_a1 :
    (reducedIntegralCurve l).a₁ = 1 := by
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalCurve_a1 l

@[simp] theorem reducedIntegralCurve_a2 :
    (reducedIntegralCurve l).a₂ = 0 := by
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalCurve_a2 l

@[simp] theorem reducedIntegralCurve_a3 :
    (reducedIntegralCurve l).a₃ = 0 := by
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalCurve_a3 l

@[simp] theorem reducedIntegralCurve_a4 :
    (reducedIntegralCurve l).a₄ = 0 := by
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalCurve_a4 l

@[simp] theorem reducedIntegralCurve_a6 :
    (reducedIntegralCurve l).a₆ = 0 := by
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalCurve_a6 l

@[simp] theorem reducedIntegralCurve_b2 :
    (reducedIntegralCurve l).b₂ = 1 := by
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalCurve_b2 l

@[simp] theorem reducedIntegralCurve_b4 :
    (reducedIntegralCurve l).b₄ = 0 := by
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalCurve_b4 l

@[simp] theorem reducedIntegralCurve_b6 :
    (reducedIntegralCurve l).b₆ = 0 := by
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalCurve_b6 l

@[simp] theorem reducedIntegralCurve_b8 :
    (reducedIntegralCurve l).b₈ = 0 := by
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalCurve_b8 l

@[simp] theorem reducedIntegralCurve_c4 :
    (reducedIntegralCurve l).c₄ = 1 := by
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalCurve_c4 l

@[simp] theorem reducedIntegralCurve_c6 :
    (reducedIntegralCurve l).c₆ = -1 := by
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalCurve_c6 l

@[simp] theorem reducedIntegralCurve_delta :
    (reducedIntegralCurve l).Δ = 0 := by
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalCurve_delta l

theorem nodalCurve_not_isElliptic : ¬(nodalCurve l).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  simp

theorem reducedIntegralCurve_not_isElliptic :
    ¬(reducedIntegralCurve l).IsElliptic := by
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalCurve_not_isElliptic l

end ResidueEquation

section SplitPolynomial

def nodalTangentPolynomial : (ResidueField l)[X] :=
  X ^ 2 + X

theorem nodalTangentPolynomial_eq_X_mul :
    nodalTangentPolynomial l = X * (X + 1) := by
  simp [nodalTangentPolynomial, pow_two]
  ring

theorem nodalTangentPolynomial_eq_X_mul_X_add_C_one :
    nodalTangentPolynomial l = X * (X + C 1) := by
  rw [nodalTangentPolynomial_eq_X_mul]
  simp

theorem nodalTangentPolynomial_splits :
    Polynomial.Splits (nodalTangentPolynomial l) := by
  rw [nodalTangentPolynomial_eq_X_mul_X_add_C_one]
  exact Polynomial.Splits.X.mul (Polynomial.Splits.X_add_C 1)

theorem nodalTangentPolynomial_eval_zero :
    (nodalTangentPolynomial l).eval 0 = 0 := by
  simp [nodalTangentPolynomial]

theorem nodalTangentPolynomial_eval_neg_one :
    (nodalTangentPolynomial l).eval (-1) = 0 := by
  simp [nodalTangentPolynomial]

theorem nodalTangent_roots_distinct :
    (0 : ResidueField l) ≠ -1 := by
  simp

theorem nodalTangentPolynomial_monic :
    (nodalTangentPolynomial l).Monic := by
  rw [nodalTangentPolynomial_eq_X_mul_X_add_C_one]
  exact Polynomial.monic_X.mul (Polynomial.monic_X_add_C 1)

theorem nodalTangentPolynomial_natDegree :
    (nodalTangentPolynomial l).natDegree = 2 := by
  rw [nodalTangentPolynomial_eq_X_mul_X_add_C_one]
  rw [Polynomial.Monic.natDegree_mul Polynomial.monic_X
    (Polynomial.monic_X_add_C 1)]
  rw [Polynomial.natDegree_X, Polynomial.natDegree_X_add_C]

theorem nodalSplitReductionPolynomial :
    splitReductionPolynomial (nodalCurve l) = nodalTangentPolynomial l := by
  simp [splitReductionPolynomial, nodalCurve, nodalTangentPolynomial,
    WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]

theorem integralCurveSplitReductionPolynomial_map :
    (splitReductionPolynomial (integralCurve l)).map
        (IsLocalRing.residue ℤ_[l.value]) = nodalTangentPolynomial l := by
  rw [← splitReductionPolynomial_map]
  change splitReductionPolynomial (reducedIntegralCurve l) = _
  rw [reducedIntegralCurve_eq_nodalCurve]
  exact nodalSplitReductionPolynomial l

theorem integralCurveSplitReductionPolynomial_splits :
    Polynomial.Splits
      ((splitReductionPolynomial (integralCurve l)).map
        (IsLocalRing.residue ℤ_[l.value])) := by
  rw [integralCurveSplitReductionPolynomial_map]
  exact nodalTangentPolynomial_splits l

theorem canonicalIntegralModelSplitReductionPolynomial_map :
    letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_is_integral l
    (splitReductionPolynomial
        ((canonicalCurve l).integralModel ℤ_[l.value])).map
      (IsLocalRing.residue ℤ_[l.value]) = nodalTangentPolynomial l := by
  rw [canonicalCurve_integralModel_eq_integralCurve l]
  exact integralCurveSplitReductionPolynomial_map l

theorem canonicalIntegralModelSplitReductionPolynomial_splits :
    letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_is_integral l
    Polynomial.Splits
      ((splitReductionPolynomial
        ((canonicalCurve l).integralModel ℤ_[l.value])).map
          (IsLocalRing.residue ℤ_[l.value])) := by
  rw [canonicalIntegralModelSplitReductionPolynomial_map l]
  exact nodalTangentPolynomial_splits l

end SplitPolynomial

section ReductionClasses

theorem canonicalCurve_hasMultiplicativeReduction :
    (canonicalCurve l).HasMultiplicativeReduction ℤ_[l.value] := by
  letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
    canonicalCurve_is_integral l
  letI : WeierstrassCurve.IsMinimal ℤ_[l.value] (canonicalCurve l) :=
    canonicalCurve_isMinimal l
  exact
    { badReduction := canonicalCurve_delta_valuation_lt_one l
      multiplicativeReduction := canonicalCurve_c4_valuation_eq_one l }

theorem canonicalCurve_hasSplitMultiplicativeReduction :
    (canonicalCurve l).HasSplitMultiplicativeReduction ℤ_[l.value] := by
  letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
    canonicalCurve_is_integral l
  letI : WeierstrassCurve.IsMinimal ℤ_[l.value] (canonicalCurve l) :=
    canonicalCurve_isMinimal l
  letI : (canonicalCurve l).HasMultiplicativeReduction ℤ_[l.value] :=
    canonicalCurve_hasMultiplicativeReduction l
  refine { splitMultiplicativeReduction := ?_ }
  change Polynomial.Splits
    ((splitReductionPolynomial
      ((canonicalCurve l).integralModel ℤ_[l.value])).map
        (IsLocalRing.residue ℤ_[l.value]))
  exact canonicalIntegralModelSplitReductionPolynomial_splits l

theorem canonicalCurve_hasMultiplicativeReductionOnMinimalModel :
    HasMultiplicativeReductionOnMinimalModel ℤ_[l.value]
      (canonicalCurve l) := by
  exact ⟨1, by simpa using canonicalCurve_hasMultiplicativeReduction l⟩

theorem canonicalCurve_hasSplitMultiplicativeReductionOnMinimalModel :
    HasSplitMultiplicativeReductionOnMinimalModel ℤ_[l.value]
      (canonicalCurve l) := by
  exact ⟨1, by simpa using canonicalCurve_hasSplitMultiplicativeReduction l⟩

theorem canonicalCurve_hasStableReductionOnMinimalModel :
    TateCurve.HasStableReductionOnMinimalModel ℤ_[l.value]
      (canonicalCurve l) :=
  Or.inr (canonicalCurve_hasMultiplicativeReductionOnMinimalModel l)

theorem canonicalCurve_not_hasGoodReduction :
    ¬(canonicalCurve l).HasGoodReduction ℤ_[l.value] := by
  exact (canonicalCurve_hasMultiplicativeReduction l).not_hasGoodReduction

theorem canonicalCurve_not_hasAdditiveReduction :
    ¬(canonicalCurve l).HasAdditiveReduction ℤ_[l.value] := by
  exact (canonicalCurve_hasMultiplicativeReduction l).not_hasAdditiveReduction

theorem canonicalCurve_reduction_eq_nodalCurve :
    letI : WeierstrassCurve.IsMinimal ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_isMinimal l
    (canonicalCurve l).reduction ℤ_[l.value] = nodalCurve l := by
  letI : WeierstrassCurve.IsIntegral ℤ_[l.value] (canonicalCurve l) :=
    canonicalCurve_is_integral l
  rw [WeierstrassCurve.reduction,
    canonicalCurve_integralModel_eq_integralCurve l]
  exact reducedIntegralCurve_eq_nodalCurve l

theorem canonicalCurve_reduction_not_isElliptic :
    letI : WeierstrassCurve.IsMinimal ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_isMinimal l
    ¬((canonicalCurve l).reduction ℤ_[l.value]).IsElliptic := by
  rw [canonicalCurve_reduction_eq_nodalCurve l]
  exact nodalCurve_not_isElliptic l

theorem canonicalCurve_reduction_delta_eq_zero :
    letI : WeierstrassCurve.IsMinimal ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_isMinimal l
    ((canonicalCurve l).reduction ℤ_[l.value]).Δ = 0 := by
  rw [canonicalCurve_reduction_eq_nodalCurve l]
  exact nodalCurve_delta l

theorem canonicalCurve_reduction_c4_eq_one :
    letI : WeierstrassCurve.IsMinimal ℤ_[l.value] (canonicalCurve l) :=
      canonicalCurve_isMinimal l
    ((canonicalCurve l).reduction ℤ_[l.value]).c₄ = 1 := by
  rw [canonicalCurve_reduction_eq_nodalCurve l]
  exact nodalCurve_c4 l

def canonicalMultiplicativeCertificate :
    TateCurve.MultiplicativeCertificate ℤ_[l.value] (canonicalCurve l) where
  coordinateChange := 1
  integral := by
    simpa using canonicalCurve_is_integral l
  minimal := by
    simpa using canonicalCurve_isMinimal l
  delta_lt_one := by
    simpa using canonicalCurve_delta_valuation_lt_one l
  c₄_eq_one := by
    simpa using canonicalCurve_c4_valuation_eq_one l

theorem canonicalMultiplicativeCertificate_transformed :
    (canonicalMultiplicativeCertificate l).transformed = canonicalCurve l := by
  simp [canonicalMultiplicativeCertificate,
    TateCurve.MultiplicativeCertificate.transformed]

theorem canonicalMultiplicativeCertificate_source_predicate :
    HasMultiplicativeReductionOnMinimalModel ℤ_[l.value]
      (canonicalCurve l) :=
  (canonicalMultiplicativeCertificate l).hasMultiplicativeReductionOnMinimalModel

theorem canonicalMultiplicativeCertificate_stable :
    TateCurve.HasStableReductionOnMinimalModel ℤ_[l.value]
      (canonicalCurve l) :=
  TateCurve.multiplicative_certificate_stable (R := ℤ_[l.value])
    (canonicalMultiplicativeCertificate l)

end ReductionClasses

namespace NodalNormalization

variable {k : Type*} [Field k]

def OnCurve (x y : k) : Prop := y ^ 2 + x * y = x ^ 3

def xCoordinate (t : k) : k := t * (t + 1)

def yCoordinate (t : k) : k := t * xCoordinate t

def point (t : k) : k × k := (xCoordinate t, yCoordinate t)

@[simp] theorem point_fst (t : k) : (point t).1 = xCoordinate t := rfl

@[simp] theorem point_snd (t : k) : (point t).2 = yCoordinate t := rfl

theorem parameter_satisfies (t : k) :
    OnCurve (xCoordinate t) (yCoordinate t) := by
  simp only [OnCurve, xCoordinate, yCoordinate]
  ring

theorem point_satisfies (t : k) : OnCurve (point t).1 (point t).2 :=
  parameter_satisfies t

@[simp] theorem xCoordinate_zero : xCoordinate (0 : k) = 0 := by
  simp [xCoordinate]

@[simp] theorem yCoordinate_zero : yCoordinate (0 : k) = 0 := by
  simp [yCoordinate]

@[simp] theorem xCoordinate_neg_one : xCoordinate (-1 : k) = 0 := by
  simp [xCoordinate]

@[simp] theorem yCoordinate_neg_one : yCoordinate (-1 : k) = 0 := by
  simp [yCoordinate]

@[simp] theorem point_zero : point (0 : k) = (0, 0) := by
  simp [point]

@[simp] theorem point_neg_one : point (-1 : k) = (0, 0) := by
  simp [point]

theorem branch_parameters_distinct : (0 : k) ≠ -1 := by
  simp

theorem xCoordinate_eq_zero_iff (t : k) :
    xCoordinate t = 0 ↔ t = 0 ∨ t = -1 := by
  rw [xCoordinate, mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using eq_neg_of_add_eq_zero_left h)
  · intro h
    rcases h with rfl | rfl
    · simp
    · simp

theorem point_eq_node_iff (t : k) :
    point t = (0, 0) ↔ t = 0 ∨ t = -1 := by
  constructor
  · intro h
    have hx : xCoordinate t = 0 := by
      simpa [point] using congrArg Prod.fst h
    exact (xCoordinate_eq_zero_iff t).mp hx
  · intro h
    rcases h with rfl | rfl <;> simp

theorem yCoordinate_eq_t_mul_xCoordinate (t : k) :
    yCoordinate t = t * xCoordinate t := rfl

theorem xCoordinate_ne_zero_iff (t : k) :
    xCoordinate t ≠ 0 ↔ t ≠ 0 ∧ t ≠ -1 := by
  rw [ne_eq, xCoordinate_eq_zero_iff, not_or]

theorem parameter_ne_branches_of_xCoordinate_ne_zero {t : k}
    (ht : xCoordinate t ≠ 0) : t ≠ 0 ∧ t ≠ -1 :=
  (xCoordinate_ne_zero_iff t).mp ht

theorem xCoordinate_ne_zero_of_parameter_ne_branches {t : k}
    (ht : t ≠ 0 ∧ t ≠ -1) : xCoordinate t ≠ 0 :=
  (xCoordinate_ne_zero_iff t).mpr ht

theorem recover_parameter_from_normalized_point {t : k}
    (ht : xCoordinate t ≠ 0) :
    yCoordinate t / xCoordinate t = t := by
  rw [yCoordinate]
  field_simp

theorem recover_x {x y : k} (hxy : OnCurve x y) (hx : x ≠ 0) :
    x = (y / x) * (y / x + 1) := by
  rw [OnCurve] at hxy
  calc
    x = x ^ 3 / x ^ 2 := by field_simp
    _ = (y ^ 2 + x * y) / x ^ 2 := by rw [hxy]
    _ = (y / x) * (y / x + 1) := by field_simp

theorem recover_y {x y : k} (hx : x ≠ 0) :
    y = (y / x) * x := by
  field_simp

theorem recover_point {x y : k} (hxy : OnCurve x y) (hx : x ≠ 0) :
    point (y / x) = (x, y) := by
  have hxc : xCoordinate (y / x) = x := by
    change (y / x) * (y / x + 1) = x
    exact (recover_x hxy hx).symm
  apply Prod.ext
  · change xCoordinate (y / x) = x
    exact hxc
  · change yCoordinate (y / x) = y
    change (y / x) * xCoordinate (y / x) = y
    rw [hxc]
    exact (recover_y hx).symm

theorem parameter_unique_off_node {s t : k}
    (hs : xCoordinate s ≠ 0)
    (hpoint : point s = point t) : s = t := by
  have hy := congrArg Prod.snd hpoint
  have hx := congrArg Prod.fst hpoint
  have hy' : yCoordinate s = yCoordinate t := by simpa [point] using hy
  have hx' : xCoordinate s = xCoordinate t := by simpa [point] using hx
  have hratio : yCoordinate s / xCoordinate s =
      yCoordinate t / xCoordinate t := by rw [hy', hx']
  rw [recover_parameter_from_normalized_point hs] at hratio
  have ht : xCoordinate t ≠ 0 := by
    intro ht
    exact hs (hx'.trans ht)
  rw [recover_parameter_from_normalized_point ht] at hratio
  exact hratio

theorem point_injective_away_from_branches {s t : k}
    (hs : s ≠ 0 ∧ s ≠ -1)
    (hpoint : point s = point t) : s = t := by
  apply parameter_unique_off_node
    (xCoordinate_ne_zero_of_parameter_ne_branches hs) hpoint

theorem onCurve_zero : OnCurve (0 : k) 0 := by
  simp [OnCurve]

theorem onCurve_x_axis_iff (x : k) :
    OnCurve x 0 ↔ x = 0 := by
  constructor
  · intro h
    have hpow : x ^ 3 = 0 := by simpa [OnCurve] using h.symm
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hpow
  · intro hx
    subst x
    simp [OnCurve]

theorem onCurve_y_axis_iff (y : k) :
    OnCurve 0 y ↔ y = 0 := by
  simp [OnCurve]

theorem yCoordinate_add_xCoordinate (t : k) :
    yCoordinate t + xCoordinate t = (t + 1) * xCoordinate t := by
  simp [yCoordinate]
  ring

theorem branch_zero_tangent_factor :
    yCoordinate (0 : k) = 0 := by simp

theorem branch_neg_one_tangent_factor :
    yCoordinate (-1 : k) + xCoordinate (-1 : k) = 0 := by simp

end NodalNormalization

section ResidueNormalization

def reducedNodalX (t : ResidueField l) : ResidueField l :=
  NodalNormalization.xCoordinate t

def reducedNodalY (t : ResidueField l) : ResidueField l :=
  NodalNormalization.yCoordinate t

def reducedNodalPoint (t : ResidueField l) :
    ResidueField l × ResidueField l :=
  NodalNormalization.point t

theorem reducedNodalPoint_satisfies (t : ResidueField l) :
    NodalNormalization.OnCurve
      (reducedNodalPoint l t).1 (reducedNodalPoint l t).2 :=
  NodalNormalization.point_satisfies t

theorem reducedNodalPoint_eq_node_iff (t : ResidueField l) :
    reducedNodalPoint l t = (0, 0) ↔ t = 0 ∨ t = -1 :=
  NodalNormalization.point_eq_node_iff t

theorem reducedNodalBranchesDistinct :
    (0 : ResidueField l) ≠ -1 :=
  NodalNormalization.branch_parameters_distinct

theorem reducedNodalPoint_injective_off_node {s t : ResidueField l}
    (hs : s ≠ 0 ∧ s ≠ -1)
    (hpoint : reducedNodalPoint l s = reducedNodalPoint l t) : s = t :=
  NodalNormalization.point_injective_away_from_branches hs hpoint

theorem reducedNodalPoint_recovers_off_node {x y : ResidueField l}
    (hxy : NodalNormalization.OnCurve x y) (hx : x ≠ 0) :
    reducedNodalPoint l (y / x) = (x, y) :=
  NodalNormalization.recover_point hxy hx

end ResidueNormalization

section Output

structure CanonicalLocalReductionPacket where
  curve : WeierstrassCurve ℚ_[l.value]
  curve_eq : curve = canonicalCurve l
  integral : WeierstrassCurve.IsIntegral ℤ_[l.value] curve
  minimal : WeierstrassCurve.IsMinimal ℤ_[l.value] curve
  elliptic : curve.IsElliptic
  delta_nonzero : curve.Δ ≠ 0
  delta_valuation_lt_one :
    (IsDiscreteValuationRing.maximalIdeal ℤ_[l.value]).valuation
      ℚ_[l.value] curve.Δ < 1
  c4_valuation_eq_one :
    (IsDiscreteValuationRing.maximalIdeal ℤ_[l.value]).valuation
      ℚ_[l.value] curve.c₄ = 1
  multiplicative : curve.HasMultiplicativeReduction ℤ_[l.value]
  splitMultiplicative : curve.HasSplitMultiplicativeReduction ℤ_[l.value]
  reducedCurve : WeierstrassCurve (ResidueField l)
  reducedCurve_eq : reducedCurve = nodalCurve l
  tangentPolynomial : (ResidueField l)[X]
  tangentPolynomial_eq : tangentPolynomial = X * (X + C 1)
  tangentSplits : Polynomial.Splits tangentPolynomial

def canonicalLocalReductionPacket : CanonicalLocalReductionPacket l where
  curve := canonicalCurve l
  curve_eq := rfl
  integral := canonicalCurve_is_integral l
  minimal := canonicalCurve_isMinimal l
  elliptic := canonicalCurve_is_elliptic l
  delta_nonzero := canonicalCurve_delta_ne_zero l
  delta_valuation_lt_one := canonicalCurve_delta_valuation_lt_one l
  c4_valuation_eq_one := canonicalCurve_c4_valuation_eq_one l
  multiplicative := canonicalCurve_hasMultiplicativeReduction l
  splitMultiplicative := canonicalCurve_hasSplitMultiplicativeReduction l
  reducedCurve := reducedIntegralCurve l
  reducedCurve_eq := reducedIntegralCurve_eq_nodalCurve l
  tangentPolynomial := nodalTangentPolynomial l
  tangentPolynomial_eq := nodalTangentPolynomial_eq_X_mul_X_add_C_one l
  tangentSplits := nodalTangentPolynomial_splits l

theorem canonicalLocalReductionPacket_curve :
    (canonicalLocalReductionPacket l).curve = canonicalCurve l := rfl

theorem canonicalLocalReductionPacket_isIntegral :
    WeierstrassCurve.IsIntegral ℤ_[l.value]
      (canonicalLocalReductionPacket l).curve :=
  (canonicalLocalReductionPacket l).integral

theorem canonicalLocalReductionPacket_isMinimal :
    WeierstrassCurve.IsMinimal ℤ_[l.value]
      (canonicalLocalReductionPacket l).curve :=
  (canonicalLocalReductionPacket l).minimal

theorem canonicalLocalReductionPacket_isElliptic :
    (canonicalLocalReductionPacket l).curve.IsElliptic :=
  (canonicalLocalReductionPacket l).elliptic

theorem canonicalLocalReductionPacket_delta_nonzero :
    (canonicalLocalReductionPacket l).curve.Δ ≠ 0 :=
  (canonicalLocalReductionPacket l).delta_nonzero

theorem canonicalLocalReductionPacket_multiplicative :
    (canonicalLocalReductionPacket l).curve.HasMultiplicativeReduction
      ℤ_[l.value] :=
  (canonicalLocalReductionPacket l).multiplicative

theorem canonicalLocalReductionPacket_splitMultiplicative :
    (canonicalLocalReductionPacket l).curve.HasSplitMultiplicativeReduction
      ℤ_[l.value] :=
  (canonicalLocalReductionPacket l).splitMultiplicative

theorem canonicalLocalReductionPacket_reducedCurve :
    (canonicalLocalReductionPacket l).reducedCurve = nodalCurve l :=
  (canonicalLocalReductionPacket l).reducedCurve_eq

theorem canonicalLocalReductionPacket_tangentSplits :
    Polynomial.Splits (canonicalLocalReductionPacket l).tangentPolynomial :=
  (canonicalLocalReductionPacket l).tangentSplits

structure ConcreteTateLocalReductionCarrier where
  localCarrier : ConcreteTateLocalCarrier l
  reduction : CanonicalLocalReductionPacket l
  parameter_eq : localCarrier.parameter.q = q l
  curve_eq : reduction.curve =
    TateCurve.weierstrassCurve ℚ_[l.value] localCarrier.parameter.q

def concreteTateLocalReductionCarrier :
    ConcreteTateLocalReductionCarrier l where
  localCarrier := ConcreteTateLocalCarrier.canonical l
  reduction := canonicalLocalReductionPacket l
  parameter_eq := by
    rw [ConcreteTateLocalCarrier.canonical_q_eq_prime]
    rfl
  curve_eq := by
    rw [ConcreteTateLocalCarrier.canonical_q_eq_prime]
    rfl

theorem concreteTateLocalReductionCarrier_parameter :
    (concreteTateLocalReductionCarrier l).localCarrier.parameter.q = q l :=
  (concreteTateLocalReductionCarrier l).parameter_eq

theorem concreteTateLocalReductionCarrier_curve :
    (concreteTateLocalReductionCarrier l).reduction.curve =
      TateCurve.weierstrassCurve ℚ_[l.value]
        (concreteTateLocalReductionCarrier l).localCarrier.parameter.q :=
  (concreteTateLocalReductionCarrier l).curve_eq

theorem concreteTateLocalReductionCarrier_splitMultiplicative :
    ((concreteTateLocalReductionCarrier l).reduction.curve).HasSplitMultiplicativeReduction
      ℤ_[l.value] :=
  (concreteTateLocalReductionCarrier l).reduction.splitMultiplicative

theorem concreteTateLocalReductionCarrier_stable :
    TateCurve.HasStableReductionOnMinimalModel ℤ_[l.value]
      (concreteTateLocalReductionCarrier l).reduction.curve := by
  rw [(concreteTateLocalReductionCarrier l).reduction.curve_eq]
  exact canonicalCurve_hasStableReductionOnMinimalModel l

end Output

end TateCurvePadic

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def tateCurveLocalReduction : Obligation :=
  { id := "Foundations.Geometry.tate-curve-local-reduction"
    source := "IUT I, Definition 3.1(b)-(c); split multiplicative Tate place"
    status := VerificationStatus.proved
    note :=
      "For q equal to p in Q_p, p >= 5, the explicit integral q-series " ++
        "equation is proved minimal, multiplicative, and split " ++
        "multiplicative. Its reduced equation is y^2 + xy = x^3, the " ++
        "split tangent polynomial is T(T+1), and the two normalization " ++
        "parameters above the node are proved to be 0 and -1. This is not " ++
        "an identification with a separately supplied number-field curve " ++
        "and does not assert Tate analytic uniformization."
    dependsOn :=
      [ "Foundations.Geometry.tate-curve-discriminant-estimates",
        "Foundations.Geometry.elliptic-reduction-base-change",
        "Foundations.Geometry.concrete-tate-local-carrier" ] }

end LeanFormal.IUT.Audit
