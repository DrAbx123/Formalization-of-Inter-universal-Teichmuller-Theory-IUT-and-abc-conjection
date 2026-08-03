import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-! Conditional arithmetic endpoint of the Corollary 3.12 wall. -/

namespace LeanFormal.IUT

theorem cor312Conclusion_of_contract (contract : StepXIContract) :
    Cor312Conclusion contract :=
  cor312_of_constructed_stepXI contract

end LeanFormal.IUT
