import LeanFormal.IUT.ABCBridge.Statement

/-!
  Expected-failure check.  This file intentionally has no proof of ABC.
  Running `lake env lean verification/abc_without_sorry.lean` must fail with
  an unsolved goal.  It is outside the LeanFormal library on purpose.
-/

namespace LeanFormal.IUT

theorem abc_conjecture_no_sorry : ABCConjecture := by
  intro epsilon hepsilon
  -- The standard conjecture has no proof supplied here.

end LeanFormal.IUT
