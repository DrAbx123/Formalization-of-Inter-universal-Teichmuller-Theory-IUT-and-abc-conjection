/-
  A concrete initial-theta finite-place boundary.

  The rational split-multiplicative curve is transported to the Gaussian
  number field used by the checked arithmetic example.  An upstairs finite
  place is obtained from the actual lying-over theorem, and stable reduction
  is transported through the proved completion/base-change maps.  The
  resulting input uses the already proved DVR q-candidate existence theorem;
  it does not assert a Tate uniformization.
-/

import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTI.InitialTheta.FinitePlaceInput
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace

namespace LeanFormal.IUT

noncomputable section

local instance gaussianPolynomial_irreducible_fact_concrete :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

def concreteGaussianInitialThetaArithmeticData (l : PrimeGeFive) :
    InitialThetaArithmeticData l where
  Fmod := GaussianField
  F := GaussianField
  K := GaussianField
  tower := gaussianIdentityThetaTower l
  curve := concreteSplitPuncturedCurve.baseChange GaussianField

@[simp] theorem concreteGaussianInitialThetaArithmeticData_curve
    (l : PrimeGeFive) :
    (concreteGaussianInitialThetaArithmeticData l).curve =
      concreteSplitPuncturedCurve.baseChange GaussianField :=
  rfl

def concreteGaussianFivePlace : NumberField.FinitePlace GaussianField :=
  Classical.choose
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := GaussianField) concreteFivePlace)

theorem concreteGaussianFivePlace_comap :
    NumberFieldFinitePlace.comap (k := ℚ) concreteGaussianFivePlace =
      concreteFivePlace :=
  Classical.choose_spec
    (NumberFieldFinitePlace.comap_surjective
      (k := ℚ) (K := GaussianField) concreteFivePlace)

theorem concreteGaussianFivePlace_hasMultiplicativeReduction
    (l : PrimeGeFive) :
    (concreteGaussianInitialThetaArithmeticData l).curve.HasMultiplicativeReductionAt
      concreteGaussianFivePlace := by
  change (concreteSplitPuncturedCurve.baseChange GaussianField).HasMultiplicativeReductionAt
    concreteGaussianFivePlace
  apply PuncturedEllipticCurve.hasMultiplicativeReductionAt_baseChange
  rw [concreteGaussianFivePlace_comap]
  exact concreteSplitPuncturedCurve_hasMultiplicativeReductionAt_five

theorem concreteGaussianFivePlace_hasSplitMultiplicativeReduction
    (l : PrimeGeFive) :
    (concreteGaussianInitialThetaArithmeticData l).curve.HasSplitMultiplicativeReductionAt
      concreteGaussianFivePlace := by
  change (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt
    concreteGaussianFivePlace
  apply PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
  rw [concreteGaussianFivePlace_comap]
  exact concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_five

theorem concreteGaussianFivePlace_hasStableReduction
    (l : PrimeGeFive) :
    (concreteGaussianInitialThetaArithmeticData l).curve.HasStableReductionAt
      concreteGaussianFivePlace := by
  exact Or.inr (concreteGaussianFivePlace_hasMultiplicativeReduction l)

noncomputable def concreteGaussianInitialThetaFinitePlaceInput
    (l : PrimeGeFive) :
    InitialThetaFinitePlaceInput l :=
  InitialThetaFinitePlaceInput.ofStable l
    (concreteGaussianInitialThetaArithmeticData l)
    concreteGaussianFivePlace
    (concreteGaussianFivePlace_hasStableReduction l)

@[simp] theorem concreteGaussianInitialThetaFinitePlaceInput_arithmetic
    (l : PrimeGeFive) :
    (concreteGaussianInitialThetaFinitePlaceInput l).arithmetic =
      concreteGaussianInitialThetaArithmeticData l :=
  rfl

@[simp] theorem concreteGaussianInitialThetaFinitePlaceInput_place
    (l : PrimeGeFive) :
    (concreteGaussianInitialThetaFinitePlaceInput l).place =
      concreteGaussianFivePlace :=
  rfl

theorem concreteGaussianInitialThetaFinitePlaceInput_q_order_pos
    (l : PrimeGeFive) :
    0 < (concreteGaussianInitialThetaFinitePlaceInput l).qCandidate.order :=
  InitialThetaFinitePlaceInput.q_order_pos
    (concreteGaussianInitialThetaFinitePlaceInput l)

theorem concreteGaussianInitialThetaFinitePlaceInput_q_ne_one
    (l : PrimeGeFive) :
    (concreteGaussianInitialThetaFinitePlaceInput l).qCandidate.q ≠ 1 :=
  InitialThetaFinitePlaceInput.q_ne_one
    (concreteGaussianInitialThetaFinitePlaceInput l)

theorem concreteGaussianInitialThetaFinitePlaceInput_stable
    (l : PrimeGeFive) :
    (concreteGaussianInitialThetaFinitePlaceInput l).arithmetic.curve.HasStableReductionAt
      (concreteGaussianInitialThetaFinitePlaceInput l).place :=
  (concreteGaussianInitialThetaFinitePlaceInput l).stableReduction

theorem concreteGaussianInitialThetaFinitePlaceInput_multiplicative
    (l : PrimeGeFive) :
    ((concreteGaussianInitialThetaFinitePlaceInput l).arithmetic.curve).HasMultiplicativeReductionAt
      (concreteGaussianInitialThetaFinitePlaceInput l).place := by
  change (concreteGaussianInitialThetaArithmeticData l).curve.HasMultiplicativeReductionAt
    concreteGaussianFivePlace
  exact concreteGaussianFivePlace_hasMultiplicativeReduction l

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteInitialThetaFinitePlaceBoundary : Obligation :=
  { id := "IUT-I.concrete-initial-theta-finite-place-boundary"
    source := "IUT I, Definition 3.1(b); lying-over and stable reduction"
    status := VerificationStatus.testCarrier
    note :=
      "The checked Q curve and its actual finite place above 5 are lifted " ++
        "to the Gaussian number field by Mathlib's genuine lying-over " ++
        "construction. The base-changed curve is proved multiplicative, split " ++
        "multiplicative, and stable at that place, and the resulting typed " ++
        "InitialThetaFinitePlaceInput is assembled using the proved DVR " ++
        "q-candidate existence theorem. No Tate uniformization or point-level " ++
        "Galois identification is asserted."
    dependsOn :=
      [ "IUT-I.initial-theta-concrete-gaussian",
        "Foundations.Geometry.concrete-split-curve-five-place",
        "Foundations.NumberField.finite-places",
        "Foundations.Geometry.elliptic-reduction-base-change" ] }

end LeanFormal.IUT.Audit
