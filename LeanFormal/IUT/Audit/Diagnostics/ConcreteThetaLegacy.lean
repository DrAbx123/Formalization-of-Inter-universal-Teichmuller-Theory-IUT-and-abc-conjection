import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
  Concrete arithmetic extracted from the paper's theta-value discussion.

  This is not the full etale theta function.  It is the exact finite/Gaussian
  kernel used repeatedly in IUT II--III: labels have a square exponent and
  the sign involution `j -> -j` leaves that exponent unchanged.
-/

namespace LeanFormal.IUT

abbrev Fl (l : Nat) := ZMod l

def lStar (l : Nat) : Nat := (l - 1) / 2

def gaussExponent (j : Int) : Int := j ^ 2

@[simp] theorem gaussExponent_neg (j : Int) :
    gaussExponent (-j) = gaussExponent j := by
  simp [gaussExponent]

theorem gaussExponent_nonneg (j : Int) : 0 ≤ gaussExponent j := by
  exact sq_nonneg j

def thetaValue (q : Real) (j : Int) : Real :=
  q ^ (gaussExponent j).toNat

@[simp] theorem thetaValue_zero (q : Real) : thetaValue q 0 = 1 := by
  simp [thetaValue, gaussExponent]

@[simp] theorem thetaValue_neg (q : Real) (j : Int) :
    thetaValue q (-j) = thetaValue q j := by
  simp [thetaValue, gaussExponent_neg]

theorem thetaValue_pos {q : Real} (hq : 0 < q) (j : Int) :
    0 < thetaValue q j := by
  exact pow_pos hq _

theorem log_thetaValue {q : Real} (hq : 0 < q) (j : Int) :
    Real.log (thetaValue q j) = (gaussExponent j).toNat * Real.log q := by
  rw [thetaValue, Real.log_pow]
  exact (ne_of_gt hq)

theorem square_label_preserves_value {q : Real} (j : Int) :
    thetaValue q (-j) = thetaValue q j :=
  thetaValue_neg q j

end LeanFormal.IUT
