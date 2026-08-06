import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.Foundations.Geometry.WeierstrassModel
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

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
  linarith

local instance gaussianPolynomial_irreducible_fact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := by
  apply Fact.mk
  apply X_pow_sub_C_irreducible_of_prime (p := 2) Nat.prime_two
  intro b hb
  have hnonneg : 0 ≤ b ^ 2 := sq_nonneg b
  linarith

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

example (l : PrimeGeFive) :
    HasSqrtNegOne (gaussianInitialThetaArithmeticData l).F :=
  (gaussianInitialThetaArithmeticData l).tower.sqrtNegOne

end
end LeanFormal.IUT
