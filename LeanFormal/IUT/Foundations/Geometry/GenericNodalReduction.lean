import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import LeanFormal.IUT.Foundations.Geometry.TateCurveLocalReduction

namespace LeanFormal.IUT

open Polynomial

noncomputable section

structure NodalReductionEquation
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] where
  model : WeierstrassCurve R
  a₁_residue : IsLocalRing.residue R model.a₁ = 1
  a₂_residue : IsLocalRing.residue R model.a₂ = 0
  a₃_residue : IsLocalRing.residue R model.a₃ = 0
  a₄_residue : IsLocalRing.residue R model.a₄ = 0
  a₆_residue : IsLocalRing.residue R model.a₆ = 0
  b₂_residue : IsLocalRing.residue R model.b₂ = 1
  b₄_residue : IsLocalRing.residue R model.b₄ = 0
  b₆_residue : IsLocalRing.residue R model.b₆ = 0
  c₄_residue : IsLocalRing.residue R model.c₄ = 1

namespace NodalReductionEquation

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

def residueCurve (data : NodalReductionEquation R) :
    WeierstrassCurve (IsLocalRing.ResidueField R) :=
  data.model.map (IsLocalRing.residue R)

def nodalCurve (k : Type*) [Field k] : WeierstrassCurve k :=
  WeierstrassCurve.mk 1 0 0 0 0

theorem residueCurve_a1 (data : NodalReductionEquation R) :
    (data.residueCurve).a₁ = 1 := by
  simp [residueCurve, data.a₁_residue]

theorem residueCurve_a2 (data : NodalReductionEquation R) :
    (data.residueCurve).a₂ = 0 := by
  simp [residueCurve, data.a₂_residue]

theorem residueCurve_a3 (data : NodalReductionEquation R) :
    (data.residueCurve).a₃ = 0 := by
  simp [residueCurve, data.a₃_residue]

theorem residueCurve_a4 (data : NodalReductionEquation R) :
    (data.residueCurve).a₄ = 0 := by
  simp [residueCurve, data.a₄_residue]

theorem residueCurve_a6 (data : NodalReductionEquation R) :
    (data.residueCurve).a₆ = 0 := by
  simp [residueCurve, data.a₆_residue]

theorem residueCurve_b2 (data : NodalReductionEquation R) :
    (data.residueCurve).b₂ = 1 := by
  simpa [residueCurve, WeierstrassCurve.map_b₂] using data.b₂_residue

theorem residueCurve_b4 (data : NodalReductionEquation R) :
    (data.residueCurve).b₄ = 0 := by
  simpa [residueCurve, WeierstrassCurve.map_b₄] using data.b₄_residue

theorem residueCurve_b6 (data : NodalReductionEquation R) :
    (data.residueCurve).b₆ = 0 := by
  simpa [residueCurve, WeierstrassCurve.map_b₆] using data.b₆_residue

theorem residueCurve_c4 (data : NodalReductionEquation R) :
    (data.residueCurve).c₄ = 1 := by
  simpa [residueCurve, WeierstrassCurve.map_c₄] using data.c₄_residue

theorem residueCurve_eq_nodalCurve (data : NodalReductionEquation R) :
    data.residueCurve = nodalCurve (IsLocalRing.ResidueField R) := by
  ext <;> simp [residueCurve, nodalCurve,
    data.a₁_residue, data.a₂_residue, data.a₃_residue,
    data.a₄_residue, data.a₆_residue]

def tangentPolynomial (data : NodalReductionEquation R) :
    (IsLocalRing.ResidueField R)[X] :=
  splitReductionPolynomial data.residueCurve

theorem tangentPolynomial_eq_X_mul_X_add_C_one
    (data : NodalReductionEquation R) :
    data.tangentPolynomial = X * (X + C 1) := by
  simp [tangentPolynomial, splitReductionPolynomial,
    residueCurve, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄,
    WeierstrassCurve.map_b₆, WeierstrassCurve.map_c₄,
    data.a₁_residue, data.a₂_residue, data.b₂_residue,
    data.b₄_residue, data.b₆_residue, data.c₄_residue]
  ring

theorem tangentPolynomial_splits (data : NodalReductionEquation R) :
    Polynomial.Splits data.tangentPolynomial := by
  rw [tangentPolynomial_eq_X_mul_X_add_C_one]
  exact Polynomial.Splits.X.mul (Polynomial.Splits.X_add_C 1)

theorem tangentPolynomial_monic (data : NodalReductionEquation R) :
    data.tangentPolynomial.Monic := by
  rw [tangentPolynomial_eq_X_mul_X_add_C_one]
  exact Polynomial.monic_X.mul (Polynomial.monic_X_add_C 1)

theorem tangentPolynomial_natDegree (data : NodalReductionEquation R) :
    data.tangentPolynomial.natDegree = 2 := by
  rw [tangentPolynomial_eq_X_mul_X_add_C_one]
  rw [Polynomial.Monic.natDegree_mul Polynomial.monic_X
    (Polynomial.monic_X_add_C 1)]
  rw [Polynomial.natDegree_X, Polynomial.natDegree_X_add_C]

def normalizedPoint (_data : NodalReductionEquation R)
    (t : IsLocalRing.ResidueField R) :
      IsLocalRing.ResidueField R × IsLocalRing.ResidueField R :=
  TateCurvePadic.NodalNormalization.point t

theorem normalizedPoint_onCurve (data : NodalReductionEquation R)
    (t : IsLocalRing.ResidueField R) :
    TateCurvePadic.NodalNormalization.OnCurve (data.normalizedPoint t).1
      (data.normalizedPoint t).2 := by
    exact TateCurvePadic.NodalNormalization.point_satisfies t

theorem normalizedPoint_eq_node_iff (data : NodalReductionEquation R)
    (t : IsLocalRing.ResidueField R) :
    data.normalizedPoint t = (0, 0) ↔ t = 0 ∨ t = -1 := by
  exact TateCurvePadic.NodalNormalization.point_eq_node_iff t

theorem branches_distinct (_data : NodalReductionEquation R) :
    (0 : IsLocalRing.ResidueField R) ≠ -1 := by
  exact TateCurvePadic.NodalNormalization.branch_parameters_distinct

theorem normalizedPoint_injective_off_node
    (data : NodalReductionEquation R)
    {s t : IsLocalRing.ResidueField R}
    (hs : s ≠ 0 ∧ s ≠ -1)
    (hpoint : data.normalizedPoint s = data.normalizedPoint t) :
    s = t := by
  exact TateCurvePadic.NodalNormalization.point_injective_away_from_branches hs hpoint

theorem normalizedPoint_recovers_off_node
    (data : NodalReductionEquation R)
    {x y : IsLocalRing.ResidueField R}
    (hxy : TateCurvePadic.NodalNormalization.OnCurve x y) (hx : x ≠ 0) :
    data.normalizedPoint (y / x) = (x, y) := by
  exact TateCurvePadic.NodalNormalization.recover_point hxy hx

structure TangentRootPacket (data : NodalReductionEquation R) where
  zero : IsLocalRing.ResidueField R := 0
  negOne : IsLocalRing.ResidueField R := -1
  zero_root : data.tangentPolynomial.eval zero = 0
  negOne_root : data.tangentPolynomial.eval negOne = 0
  distinct : zero ≠ negOne

def tangentRootPacket (data : NodalReductionEquation R) :
    TangentRootPacket data where
  zero := 0
  negOne := -1
  zero_root := by
    rw [tangentPolynomial_eq_X_mul_X_add_C_one]
    simp
  negOne_root := by
    rw [tangentPolynomial_eq_X_mul_X_add_C_one]
    simp
  distinct := data.branches_distinct

theorem tangentRootPacket_zero (data : NodalReductionEquation R) :
    (data.tangentRootPacket).zero = 0 := rfl

theorem tangentRootPacket_negOne (data : NodalReductionEquation R) :
    (data.tangentRootPacket).negOne = -1 := rfl

theorem tangentRootPacket_zero_root (data : NodalReductionEquation R) :
    data.tangentPolynomial.eval (data.tangentRootPacket).zero = 0 :=
  data.tangentRootPacket.zero_root

theorem tangentRootPacket_negOne_root (data : NodalReductionEquation R) :
    data.tangentPolynomial.eval (data.tangentRootPacket).negOne = 0 :=
  data.tangentRootPacket.negOne_root

theorem tangentRootPacket_distinct (data : NodalReductionEquation R) :
    (data.tangentRootPacket).zero ≠ (data.tangentRootPacket).negOne :=
  data.tangentRootPacket.distinct

structure Output (data : NodalReductionEquation R) where
  curve : WeierstrassCurve (IsLocalRing.ResidueField R)
  tangent : (IsLocalRing.ResidueField R)[X]
  roots : IsLocalRing.ResidueField R × IsLocalRing.ResidueField R
  curve_eq : curve = data.residueCurve
  tangent_eq : tangent = data.tangentPolynomial
  roots_eq : roots = (0, -1)
  curve_is_nodal : curve = nodalCurve (IsLocalRing.ResidueField R)
  tangent_splits : Polynomial.Splits tangent

def output (data : NodalReductionEquation R) : Output data where
  curve := data.residueCurve
  tangent := data.tangentPolynomial
  roots := (0, -1)
  curve_eq := rfl
  tangent_eq := rfl
  roots_eq := rfl
  curve_is_nodal := data.residueCurve_eq_nodalCurve
  tangent_splits := data.tangentPolynomial_splits

theorem output_curve_eq_nodal (data : NodalReductionEquation R) :
    (data.output).curve = nodalCurve (IsLocalRing.ResidueField R) :=
  (data.output).curve_is_nodal

theorem output_tangent_splits (data : NodalReductionEquation R) :
    Polynomial.Splits (data.output).tangent :=
  (data.output).tangent_splits

end NodalReductionEquation

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def genericNodalReduction : Obligation :=
  { id := "Foundations.Geometry.generic-nodal-reduction"
    source := "IUT I, Example 3.2(i); nodal special-fiber algebra"
    status := VerificationStatus.proved
    note :=
      "A general integral Weierstrass equation with the explicit residue " ++
        "coefficient packet is reduced to y^2 + xy = x^3. Its tangent " ++
        "polynomial, roots, splitting, and normalization are proved without " ++
        "assuming a curve-specific geometric realization."
    dependsOn := ["Foundations.Geometry.reduction-base-change"] }

end LeanFormal.IUT.Audit
