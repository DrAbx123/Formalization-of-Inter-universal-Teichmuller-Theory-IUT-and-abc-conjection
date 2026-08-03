import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import LeanFormal.IUT.Foundations.Arithmetic.FiniteLabels

/-!
  The elementary Gaussian/theta kernel.

  The paper's special-value calculation has an integer label and a square
  exponent.  This file formalizes only that algebraic kernel.  The etale theta
  function, its geometric origin, and the Hodge-Arakelov comparison are not
  assumed here.

  Source correspondence: IUT II, theta-value discussion; the corresponding
  checked arithmetic kernel is `IutLean/Theta/ThetaValues.lean` in Takkun's
  repository.
-/

namespace LeanFormal.IUT

def gaussExponent (j : Int) : Int := j ^ 2

@[simp] theorem gaussExponent_neg (j : Int) :
    gaussExponent (-j) = gaussExponent j := by
  unfold gaussExponent
  ring

@[simp] theorem gaussExponent_zero : gaussExponent 0 = 0 := by
  rfl

theorem gaussExponent_nonneg (j : Int) : 0 ≤ gaussExponent j := by
  unfold gaussExponent
  exact sq_nonneg j

theorem gaussExponent_succ_sub (j : Int) :
    gaussExponent (j + 1) - gaussExponent j = 2 * j + 1 := by
  unfold gaussExponent
  ring

section Values

variable {M : Type*} [CommGroup M]

def thetaValue (q : M) (j : Int) : M :=
  q ^ gaussExponent j

@[simp] theorem thetaValue_zero (q : M) : thetaValue q 0 = 1 := by
  simp [thetaValue]

@[simp] theorem thetaValue_neg (q : M) (j : Int) :
    thetaValue q (-j) = thetaValue q j := by
  simp [thetaValue]

theorem thetaValue_eq_of_eq_neg (q : M) {j j' : Int}
    (h : j' = j ∨ j' = -j) : thetaValue q j' = thetaValue q j := by
  rcases h with h | h
  · simp [h]
  · simp [h]

theorem thetaValue_div_zero (q : M) (j : Int) :
    thetaValue q j / thetaValue q 0 = q ^ gaussExponent j := by
  simp [thetaValue]

end Values

section RealValues

def realThetaValue (q : Real) (j : Int) : Real :=
  q ^ (gaussExponent j).toNat

@[simp] theorem realThetaValue_zero (q : Real) : realThetaValue q 0 = 1 := by
  simp [realThetaValue]

@[simp] theorem realThetaValue_neg (q : Real) (j : Int) :
    realThetaValue q (-j) = realThetaValue q j := by
  simp [realThetaValue]

theorem realThetaValue_pos {q : Real} (hq : 0 < q) (j : Int) :
    0 < realThetaValue q j := by
  exact pow_pos hq _

theorem log_realThetaValue {q : Real} (j : Int) :
    Real.log (realThetaValue q j) =
      (gaussExponent j).toNat * Real.log q := by
  rw [realThetaValue, Real.log_pow]

end RealValues

section SignedLabels

/-- Bounded integer representatives for the odd-prime label interval. -/
def SignedLabel (l : Nat) :=
  {j : Int // j ∈ Set.Icc (-(lStar l : Int)) (lStar l : Int)}

noncomputable instance signedLabelFintype (l : Nat) : Fintype (SignedLabel l) :=
  (Set.finite_Icc (-(lStar l : Int)) (lStar l : Int)).fintype

namespace SignedLabel

variable {l : Nat}

def neg (j : SignedLabel l) : SignedLabel l :=
  ⟨-j.1, by
    change -(lStar l : Int) ≤ -j.1 ∧ -j.1 ≤ (lStar l : Int)
    constructor <;> linarith [j.2.1, j.2.2]⟩

@[simp] theorem neg_val (j : SignedLabel l) : (neg j).1 = -j.1 :=
  rfl

theorem neg_involutive (j : SignedLabel l) : neg (neg j) = j := by
  apply Subtype.ext
  simp

def toFl (l : Nat) (j : SignedLabel l) : Fl l :=
  j.1

theorem toFl_neg (j : SignedLabel l) : toFl l (neg j) = -(toFl l j) := by
  simp [toFl, neg]

theorem theta_neg (q : Real) (j : SignedLabel l) :
    realThetaValue q (neg j).1 = realThetaValue q j.1 := by
  simp

end SignedLabel

end SignedLabels

end LeanFormal.IUT
