import LeanFormal.IUT.ABCBridge.Statement

/-!
  Expected-success check.  The same assertion is accepted only because of the
  explicit `sorry`, and Lean reports the corresponding `sorryAx` dependency.
-/

namespace LeanFormal.IUT

theorem abc_conjecture_with_sorry : ABCConjecture := by
  sorry

#print axioms abc_conjecture_with_sorry

end LeanFormal.IUT
