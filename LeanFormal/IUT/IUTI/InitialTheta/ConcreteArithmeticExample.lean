/-
  A concrete, fully checked arithmetic input for IUT I Definition 3.1.

  This file is deliberately an example, not an existence theorem for arbitrary
  initial Theta data.  It uses the quadratic number field `Q(i)` and the
  identity field tower.  The Lean proofs below establish the field, Galois,
  finite-dimensional, square-root, and elliptic-curve obligations for this
  particular input; the source's additional reduction and anabelian conditions
  are not silently added here.
-/

import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.Foundations.Geometry.WeierstrassModel
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot

namespace LeanFormal.IUT

open Polynomial

noncomputable section

def gaussianPolynomial : Polynomial ℚ :=
  Polynomial.X ^ 2 - Polynomial.C (-1)

theorem gaussianPolynomial_irreducible : Irreducible gaussianPolynomial := by
  change Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1))
  apply X_pow_sub_C_irreducible_of_prime (p := 2) Nat.prime_two
  intro b hb
  have hnonneg : 0 ≤ b ^ 2 := sq_nonneg b
  rw [hb] at hnonneg
  exact (not_le_of_gt (neg_lt_zero.mpr zero_lt_one)) hnonneg

local instance gaussianPolynomial_irreducible_fact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := by
  apply Fact.mk
  apply X_pow_sub_C_irreducible_of_prime (p := 2) Nat.prime_two
  intro b hb
  have hnonneg : 0 ≤ b ^ 2 := sq_nonneg b
  rw [hb] at hnonneg
  exact (not_le_of_gt (neg_lt_zero.mpr zero_lt_one)) hnonneg

abbrev GaussianField :=
  AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)

instance gaussianFieldNumberField : NumberField GaussianField := inferInstance

instance gaussianFieldIsGalois : IsGalois GaussianField GaussianField := inferInstance

theorem gaussianField_sqrtNegOne : HasSqrtNegOne GaussianField := by
  refine ⟨AdjoinRoot.root
    (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ), ?_⟩
  simpa [pow_two] using
    (root_X_pow_sub_C_pow (K := ℚ) 2 (-1))

def gaussianPuncturedCurve : PuncturedEllipticCurve GaussianField := by
  let model := ellipticModelWithJ (0 : GaussianField)
  exact
    { curve := model.1
      isElliptic := model.2
      puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩ }

theorem gaussianIdentityThetaTower (l : PrimeGeFive) :
    ThetaFieldTower l GaussianField GaussianField GaussianField where
  sqrtNegOne := gaussianField_sqrtNegOne
  degreePrimeToL := by
    rw [Module.finrank_self]
    exact Nat.coprime_one_left _

def gaussianInitialThetaArithmeticData (l : PrimeGeFive) :
    InitialThetaArithmeticData l where
  Fmod := GaussianField
  F := GaussianField
  K := GaussianField
  tower := gaussianIdentityThetaTower l
  curve := gaussianPuncturedCurve

theorem gaussianInitialThetaArithmeticData_sqrtNegOne (l : PrimeGeFive) :
    HasSqrtNegOne (gaussianInitialThetaArithmeticData l).F :=
  (gaussianInitialThetaArithmeticData l).tower.sqrtNegOne

end
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteInitialThetaArithmeticExample : Obligation :=
  { id := "IUT-I.initial-theta-concrete-gaussian"
    source := "IUT I, Definition 3.1 (one explicit arithmetic input)"
    status := VerificationStatus.testCarrier
    note :=
      "The Gaussian quadratic field Q(i), identity field tower, square-root " ++
        "condition, finite/Galois instances, and a nonsingular Weierstrass " ++
        "model are constructed and checked in Lean. This is a concrete " ++
        "example only; it does not prove general initial-theta existence or " ++
        "the later reduction/anabelian conditions."
    dependsOn := ["IUT-I.initial-theta-arithmetic-data"] }

end LeanFormal.IUT.Audit
