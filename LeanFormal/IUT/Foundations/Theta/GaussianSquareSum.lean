import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.Arithmetic.FiniteLabels
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
  Finite Gaussian square-sum arithmetic used by the theta-volume
  normalization.  The statements are ordinary finite-sum identities; no
  etale theta function, Hodge theater, or IUT volume map is defined here.

  The source-facing analogue is the arithmetic part of IUT III Theorem 3.11
  and IUT IV's normalization factor.  The geometric interpretation remains a
  separate pending obligation.
-/

namespace LeanFormal.IUT

open scoped BigOperators

def gaussianSquareSum (n : Nat) : Real :=
  ∑ j ∈ Finset.range (n + 1), (j : Real) ^ 2

theorem gaussianSquareSum_formula (n : Nat) :
    gaussianSquareSum n =
      (n : Real) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero =>
      simp [gaussianSquareSum]
  | succ n ih =>
      have hrec :
          gaussianSquareSum n.succ =
            gaussianSquareSum n + ((n.succ : Nat) : Real) ^ 2 := by
        unfold gaussianSquareSum
        rw [show n.succ + 1 = (n + 1) + 1 by omega,
          Finset.sum_range_succ]
      rw [hrec, ih]
      push_cast
      ring

noncomputable def normalizedGaussianDegree (l : Nat) : Real :=
  gaussianSquareSum (lStar l) / (lStar l : Real)

theorem normalizedGaussianDegree_eq_factor (l : Nat) (hodd : Odd l)
    (hl5 : 5 ≤ l) :
    normalizedGaussianDegree l =
      (l : Real) * (l + 1) / 12 := by
  unfold normalizedGaussianDegree
  rw [gaussianSquareSum_formula]
  have hstar : 0 < lStar l := by
    unfold lStar
    omega
  have hstar_ne : (lStar l : Real) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hstar)
  have hl := two_mul_lStar_add_one l hodd
  have hlR : (l : Real) = 2 * (lStar l : Real) + 1 := by
    exact_mod_cast hl.symm
  rw [hlR]
  field_simp [hstar_ne]
  ring

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def gaussianSquareSumNormalization : Obligation :=
  { id := "IUT-III.arithmetic-gaussian-square-sum-normalization"
    source := "IUT III Theorem 3.11; IUT IV normalization factor"
    status := VerificationStatus.proved
    note :=
       "Finite square-sum and odd-label l(l+1)/12 identities are proved over Real; " ++
         "their interpretation as IUT theta or log-volume data remains pending."
    dependsOn := [ "Foundations.Arithmetic.FiniteLabels" ] }

end LeanFormal.IUT.Audit
