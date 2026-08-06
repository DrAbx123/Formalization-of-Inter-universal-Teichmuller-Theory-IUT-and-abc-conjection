import LeanFormal.IUT.Audit.Status
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
  The denominator-clearing part of IUT III, Remark 3.9.5(vii).

  The source's geometric hull and Frobenioid realization are separate
  obligations.  This module isolates the arithmetic normalization that they
  must satisfy: the common tensor degree is the product of the positive
  denominators, and the exponent of one summand is the product of all other
  denominators.  No coprimality or least-common-multiple hypothesis is used.
-/

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

structure WeightedDeterminantPacket (label : Type*) [Fintype label] where
  hullLogDegree : label → Real
  structureSheafLogDegree : Real
  denominator : label → ℕ+

namespace WeightedDeterminantPacket

variable {label : Type*} [Fintype label]
variable (packet : WeightedDeterminantPacket label)

def adjustedLogDegree (i : label) : Real :=
  packet.hullLogDegree i - packet.structureSheafLogDegree

def commonTensorDegree : ℕ :=
  by
    classical
    exact ∏ i : label, (packet.denominator i : ℕ)

def summandTensorExponent (i : label) : ℕ :=
  by
    classical
    exact ∏ j ∈ (Finset.univ.erase i), (packet.denominator j : ℕ)

theorem commonTensorDegree_pos : 0 < packet.commonTensorDegree := by
  classical
  apply Finset.prod_pos
  intro i hi
  exact (packet.denominator i).pos

theorem summandTensorExponent_pos (i : label) :
    0 < packet.summandTensorExponent i := by
  classical
  apply Finset.prod_pos
  intro j hj
  exact (packet.denominator j).pos

theorem denominator_mul_summandTensorExponent (i : label) :
    (packet.denominator i : ℕ) * packet.summandTensorExponent i =
      packet.commonTensorDegree := by
  classical
  exact Finset.mul_prod_erase Finset.univ
    (fun j => (packet.denominator j : ℕ)) (Finset.mem_univ i)

def normalizedLogVolume : Real :=
  by
    classical
    exact ∑ i : label,
      packet.adjustedLogDegree i / (packet.denominator i : Real)

def weightedLogVolume : Real :=
  by
    classical
    exact ∑ i : label,
      (packet.summandTensorExponent i : Real) * packet.adjustedLogDegree i

theorem commonTensorDegree_smul_normalizedSummand (i : label) :
    (packet.commonTensorDegree : Real) *
        (packet.adjustedLogDegree i / (packet.denominator i : Real)) =
      (packet.summandTensorExponent i : Real) *
        packet.adjustedLogDegree i := by
  have hdegree :
      (packet.commonTensorDegree : Real) =
        (packet.denominator i : Real) *
          (packet.summandTensorExponent i : Real) := by
    have hnat := packet.denominator_mul_summandTensorExponent i
    have hcast := congrArg (fun n : ℕ => (n : Real)) hnat.symm
    simpa only [Nat.cast_mul] using hcast
  have hden : (packet.denominator i : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (packet.denominator i).pos)
  rw [hdegree]
  field_simp

theorem weightedLogVolume_eq_commonTensorDegree_mul_normalizedLogVolume :
    packet.weightedLogVolume =
      (packet.commonTensorDegree : Real) * packet.normalizedLogVolume := by
  classical
  rw [weightedLogVolume, normalizedLogVolume]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact (packet.commonTensorDegree_smul_normalizedSummand i).symm

theorem denominator_two_four_commonTensorDegree :
    ∀ (packet : WeightedDeterminantPacket (Fin 2)),
      packet.denominator 0 = 2 → packet.denominator 1 = 4 →
        packet.commonTensorDegree = 8
  | packet, h0, h1 => by
      simp [commonTensorDegree, Fin.prod_univ_two, h0, h1]

end WeightedDeterminantPacket

end
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def weightedDeterminantNormalization : Obligation :=
  { id := "IUT-III.remark-3-9-5-weighted-determinant-normalization"
    source := "IUT III, Remark 3.9.5(vii), Ob3"
    status := VerificationStatus.proved
    note :=
      "The common tensor degree, complementary summand exponents, " ++
        "structure-sheaf-adjusted log degrees, and denominator-clearing " ++
        "log-volume identity are proved for finite positive denominators. " ++
        "The geometric hull, determinant line realization, and Frobenioid " ++
        "transport remain separate source obligations."
    dependsOn := ["IUT-III.holomorphic-hull-determinant-log-volume"] }

end LeanFormal.IUT.Audit
