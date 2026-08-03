import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic

/-!
  Finite weighted log-volume arithmetic.

  This is a standard finite-sum lemma used by the source-facing Stage-1
  developments.  It proves the averaging inequalities from positivity of the
  total weight; it does not assert that an IUT holomorphic hull has been
  constructed.
-/

namespace LeanFormal.IUT

open scoped BigOperators

structure WeightedValues (label : Type*) [Fintype label] where
  value : label -> Real
  weight : label -> Real
  weightTotal : Real
  weightTotal_pos : 0 < weightTotal
  weightTotal_eq_sum : weightTotal = Finset.univ.sum weight

noncomputable def WeightedValues.average {label : Type*} [Fintype label]
    (data : WeightedValues label) : Real :=
  (Finset.univ.sum fun j => data.weight j * data.value j) / data.weightTotal

theorem WeightedValues.average_le_of_pointwise
    {label : Type*} [Fintype label]
    (data : WeightedValues label)
    (hw : ∀ j, 0 ≤ data.weight j)
    {bound : Real} (hv : ∀ j, data.value j ≤ bound) :
    data.average ≤ bound := by
  unfold WeightedValues.average
  rw [div_le_iff₀ data.weightTotal_pos]
  calc
    Finset.univ.sum (fun j => data.weight j * data.value j) ≤
        Finset.univ.sum (fun j => data.weight j * bound) := by
      exact Finset.sum_le_sum (fun j _hj =>
        mul_le_mul_of_nonneg_left (hv j) (hw j))
    _ = bound * data.weightTotal := by
      calc
        Finset.univ.sum (fun j => data.weight j * bound) =
            (Finset.univ.sum data.weight) * bound := by
          simpa using
            (Finset.sum_mul (s := Finset.univ) (f := data.weight) bound).symm
        _ = bound * data.weightTotal := by
          rw [← data.weightTotal_eq_sum]
          exact mul_comm _ _

theorem WeightedValues.lower_le_average_of_pointwise
    {label : Type*} [Fintype label]
    (data : WeightedValues label)
    (hw : ∀ j, 0 ≤ data.weight j)
    {bound : Real} (hv : ∀ j, bound ≤ data.value j) :
    bound ≤ data.average := by
  unfold WeightedValues.average
  rw [le_div_iff₀ data.weightTotal_pos]
  calc
    bound * data.weightTotal =
        Finset.univ.sum (fun j => data.weight j * bound) := by
      calc
        bound * data.weightTotal = bound * (Finset.univ.sum data.weight) := by
          rw [data.weightTotal_eq_sum]
        _ = (Finset.univ.sum data.weight) * bound := by exact mul_comm _ _
        _ = Finset.univ.sum (fun j => data.weight j * bound) := by
          simpa using
            (Finset.sum_mul (s := Finset.univ) (f := data.weight) bound)
    _ ≤ Finset.univ.sum (fun j => data.weight j * data.value j) := by
      exact Finset.sum_le_sum (fun j _hj =>
        mul_le_mul_of_nonneg_left (hv j) (hw j))

end LeanFormal.IUT
