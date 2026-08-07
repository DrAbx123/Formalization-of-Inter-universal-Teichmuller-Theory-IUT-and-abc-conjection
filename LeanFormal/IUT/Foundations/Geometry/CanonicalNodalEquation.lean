import LeanFormal.IUT.Foundations.Geometry.GenericNodalReduction

namespace LeanFormal.IUT

open Polynomial

noncomputable section

namespace TateCurvePadic

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

def canonicalNodalEquation :
    NodalReductionEquation ℤ_[l.value] where
  model := integralCurve l
  a₁_residue := by
    simp [integralCurve]
  a₂_residue := by
    simp [integralCurve]
  a₃_residue := by
    simp [integralCurve]
  a₄_residue := by
    simp [integralCurve]
  a₆_residue := by
    simp [integralCurve]
  b₂_residue := by
    change (reducedIntegralCurve l).b₂ = 1
    exact reducedIntegralCurve_b2 l
  b₄_residue := by
    change (reducedIntegralCurve l).b₄ = 0
    exact reducedIntegralCurve_b4 l
  b₆_residue := by
    change (reducedIntegralCurve l).b₆ = 0
    exact reducedIntegralCurve_b6 l
  c₄_residue := by
    change (reducedIntegralCurve l).c₄ = 1
    exact reducedIntegralCurve_c4 l

theorem canonicalNodalEquation_model :
    (canonicalNodalEquation l).model = integralCurve l := rfl

theorem canonicalNodalEquation_residueCurve :
    (canonicalNodalEquation l).residueCurve = reducedIntegralCurve l := by
  rfl

theorem canonicalNodalEquation_residueCurve_eq_nodal :
    (canonicalNodalEquation l).residueCurve = nodalCurve l := by
  rw [canonicalNodalEquation_residueCurve]
  exact reducedIntegralCurve_eq_nodalCurve l

theorem canonicalNodalEquation_tangentPolynomial :
    (canonicalNodalEquation l).tangentPolynomial =
      nodalTangentPolynomial l := by
  exact (NodalReductionEquation.tangentPolynomial_eq_X_mul_X_add_C_one
    (canonicalNodalEquation l)).trans
      (nodalTangentPolynomial_eq_X_mul_X_add_C_one l).symm

theorem canonicalNodalEquation_tangentPolynomial_eq :
    (canonicalNodalEquation l).tangentPolynomial =
      X * (X + C 1) := by
  exact NodalReductionEquation.tangentPolynomial_eq_X_mul_X_add_C_one
    (canonicalNodalEquation l)

theorem canonicalNodalEquation_tangent_splits :
    Polynomial.Splits (canonicalNodalEquation l).tangentPolynomial :=
  NodalReductionEquation.tangentPolynomial_splits (canonicalNodalEquation l)

theorem canonicalNodalEquation_tangent_monic :
    (canonicalNodalEquation l).tangentPolynomial.Monic :=
  NodalReductionEquation.tangentPolynomial_monic (canonicalNodalEquation l)

theorem canonicalNodalEquation_tangent_degree :
    (canonicalNodalEquation l).tangentPolynomial.natDegree = 2 :=
  NodalReductionEquation.tangentPolynomial_natDegree (canonicalNodalEquation l)

theorem canonicalNodalEquation_normalizedPoint_onCurve
    (t : ResidueField l) :
    NodalNormalization.OnCurve
      ((canonicalNodalEquation l).normalizedPoint t).1
      ((canonicalNodalEquation l).normalizedPoint t).2 :=
  NodalReductionEquation.normalizedPoint_onCurve (canonicalNodalEquation l) t

theorem canonicalNodalEquation_normalizedPoint_node_iff
    (t : ResidueField l) :
    (canonicalNodalEquation l).normalizedPoint t = (0, 0) ↔
      t = 0 ∨ t = -1 :=
  NodalReductionEquation.normalizedPoint_eq_node_iff (canonicalNodalEquation l) t

theorem canonicalNodalEquation_normalizedPoint_injective_off_node
    {s t : ResidueField l} (hs : s ≠ 0 ∧ s ≠ -1)
    (hpoint : (canonicalNodalEquation l).normalizedPoint s =
      (canonicalNodalEquation l).normalizedPoint t) :
    s = t :=
  NodalReductionEquation.normalizedPoint_injective_off_node
    (canonicalNodalEquation l) hs hpoint

def canonicalNodalEquationOutput :
    NodalReductionEquation.Output (canonicalNodalEquation l) :=
  NodalReductionEquation.output (canonicalNodalEquation l)

theorem canonicalNodalEquationOutput_curve :
    (canonicalNodalEquationOutput l).curve = nodalCurve l := by
  exact NodalReductionEquation.output_curve_eq_nodal (canonicalNodalEquation l)

theorem canonicalNodalEquationOutput_tangent_splits :
    Polynomial.Splits (canonicalNodalEquationOutput l).tangent :=
  NodalReductionEquation.output_tangent_splits (canonicalNodalEquation l)

theorem canonicalNodalEquationOutput_tangent_eq :
    (canonicalNodalEquationOutput l).tangent = nodalTangentPolynomial l := by
  calc
    (canonicalNodalEquationOutput l).tangent =
        (canonicalNodalEquation l).tangentPolynomial := rfl
    _ = nodalTangentPolynomial l := canonicalNodalEquation_tangentPolynomial l

theorem canonicalNodalEquationOutput_roots :
    (canonicalNodalEquationOutput l).roots = (0, -1) := rfl

end TateCurvePadic

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def canonicalNodalEquation : Obligation :=
  { id := "Foundations.Geometry.canonical-nodal-equation"
    source := "IUT I, Example 3.2(i); residue equation specialization"
    status := VerificationStatus.proved
    note :=
      "The generic residue-coefficient packet is instantiated by the actual " ++
        "integral q-series equation. Its nodal curve, tangent polynomial, " ++
        "roots, splitting, and normalization are definitionally tied to the " ++
        "previously proved canonical local reduction."
    dependsOn :=
      [ "Foundations.Geometry.generic-nodal-reduction",
        "Foundations.Geometry.tate-curve-local-reduction" ] }

end LeanFormal.IUT.Audit
