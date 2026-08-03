import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-!
  Small countermodels for weakened Step-(xi) interfaces.

  They are diagnostic only.  In particular, they show that a common-container
  inequality does not force the disputed tight identification unless that
  identification is made an explicit premise.
-/

namespace LeanFormal.IUT

theorem slack_common_container :
    let q : Real := -1
    let theta : Real := -2
    let target : Real := -1
    q < 0 ∧ q ≤ target ∧ target ≤ -1 ∧ ¬ target ≤ theta := by
  norm_num

theorem same_copy_comparison_is_tautological
    {x y : Real} (hxy : x ≤ y) : x ≤ y := hxy

end LeanFormal.IUT
