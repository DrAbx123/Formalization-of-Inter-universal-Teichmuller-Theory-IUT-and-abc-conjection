import LeanFormal.IUT.Audit.Status
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
  Finite determinant and log-product arithmetic.

  These are the ordinary algebraic steps that occur inside the paper's
  determinant/tensor normalization and log-volume bookkeeping.  The module
  has no holomorphic hull, Frobenioid, or IUT-specific carrier.
-/

namespace LeanFormal.IUT

open scoped BigOperators

theorem det_diagonal_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → Real) :
    Matrix.det (Matrix.diagonal (fun i => f i * g i)) =
      Matrix.det (Matrix.diagonal f) * Matrix.det (Matrix.diagonal g) := by
  classical
  rw [Matrix.det_diagonal, Matrix.det_diagonal, Matrix.det_diagonal,
    Finset.prod_mul_distrib]

theorem det_diagonal_const_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Real) (f : ι → Real) :
    Matrix.det (Matrix.diagonal (fun i => c * f i)) =
      c ^ Fintype.card ι * Matrix.det (Matrix.diagonal f) := by
  classical
  rw [Matrix.det_diagonal, Matrix.det_diagonal]
  simp [Finset.prod_mul_distrib, Finset.prod_const, mul_comm]

theorem det_diagonal_tensor {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (f : α → Real) (g : β → Real) :
    Matrix.det (Matrix.diagonal (fun ij : α × β => f ij.1 * g ij.2)) =
      Matrix.det (Matrix.diagonal f) ^ Fintype.card β *
        Matrix.det (Matrix.diagonal g) ^ Fintype.card α := by
  classical
  rw [Matrix.det_diagonal, Matrix.det_diagonal, Matrix.det_diagonal]
  change (∏ x : α × β, f x.1 * g x.2) =
    (∏ x : α, f x) ^ Fintype.card β *
      (∏ y : β, g y) ^ Fintype.card α
  rw [← Finset.univ_product_univ,
    Finset.prod_product' (Finset.univ : Finset α) (Finset.univ : Finset β)
      (fun x y => f x * g y)]
  calc
    (∏ x : α, ∏ y : β, f x * g y) =
        ∏ x : α, (f x) ^ Fintype.card β * ∏ y : β, g y := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [← Finset.pow_card_mul_prod]
      simp only [Finset.card_univ]
    _ = (∏ x : α, (f x) ^ Fintype.card β) *
        ∏ x : α, (∏ y : β, g y) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ x : α, f x) ^ Fintype.card β *
        (∏ y : β, g y) ^ Fintype.card α := by
      rw [Finset.prod_pow, Finset.prod_const]
      simp

theorem log_prod_positive {ι : Type*} [Fintype ι]
    (f : ι → Real) (hf : ∀ i, 0 < f i) :
    Real.log (∏ i, f i) = ∑ i, Real.log (f i) := by
  classical
  exact Real.log_prod (fun i hi => (ne_of_gt (hf i)))

theorem log_const_mul_sum {ι : Type*} [Fintype ι]
    (c : Real) (f : ι → Real) (hc : 0 < c) (hf : ∀ i, 0 < f i) :
    (∑ i, Real.log (c * f i)) =
      (Fintype.card ι : Real) * Real.log c + ∑ i, Real.log (f i) := by
  classical
  have hlog : ∀ i, Real.log (c * f i) = Real.log c + Real.log (f i) := by
    intro i
    exact Real.log_mul (ne_of_gt hc) (ne_of_gt (hf i))
  simp_rw [hlog]
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_const, Finset.card_univ]

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def finiteDeterminantArithmetic : Obligation :=
  { id := "Foundations.LinearAlgebra.finite-determinant-log"
    source := "Standard determinant and finite log-volume arithmetic"
    status := VerificationStatus.proved
    note :=
      "Diagonal determinant products, positive log-product expansion, and " ++
        "constant rescaling of finite log sums are proved with Mathlib. " ++
        "Holomorphic hull and IUT source compatibility are outside this layer."
    dependsOn := [] }

end LeanFormal.IUT.Audit
