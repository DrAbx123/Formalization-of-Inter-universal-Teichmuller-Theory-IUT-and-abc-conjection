import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import LeanFormal.IUT.Foundations.Arithmetic.Radical
import LeanFormal.IUT.Foundations.Arithmetic.PrimitiveAdditive

/-!
  The integer ABC statement used as the eventual arithmetic target.

  The definition follows the usual radical form.  It is intentionally a
  definition, not a proof of ABC.  The radical is Mathlib's standard
  `UniqueFactorizationMonoid.radical`; ABC triples have positive entries, so
  the value at zero is outside the conjecture's quantified domain.
-/

namespace LeanFormal.IUT

/-!
  Use Mathlib's standard radical rather than introducing a second, locally
  defined notion.  This is the product of the distinct prime divisors, with
  the conventional value zero at zero.
-/
noncomputable abbrev radical (n : Nat) : Nat := natRadical n

abbrev IsABCTriple := PrimitiveAdditiveTriple

def ABCInequality (epsilon K : Real) (a b c : Nat) : Prop :=
  (c : Real) ≤ K * Real.rpow (radical (a * b * c) : Real) (1 + epsilon)

/-- The standard epsilon-and-constant form of the integer ABC conjecture. -/
def ABCConjecture : Prop :=
  ∀ epsilon : Real, 0 < epsilon →
    ∃ K : Real, 0 < K ∧
      ∀ a b c : Nat, IsABCTriple a b c → ABCInequality epsilon K a b c

theorem radical_zero : radical 0 = 1 := by
  exact natRadical_zero

theorem radical_pos (n : Nat) : 0 < radical n := by
  exact natRadical_pos n

theorem radical_dvd_self {n : Nat} : radical n ∣ n := by
  exact natRadical_dvd_self

theorem radical_eq_one_iff {n : Nat} : radical n = 1 ↔ n ≤ 1 := by
  exact natRadical_eq_one_iff

theorem abcInequality_is_explicit (epsilon K : Real) (a b c : Nat) :
    ABCInequality epsilon K a b c ↔
      (c : Real) ≤ K * Real.rpow (radical (a * b * c) : Real) (1 + epsilon) :=
  Iff.rfl

end LeanFormal.IUT
