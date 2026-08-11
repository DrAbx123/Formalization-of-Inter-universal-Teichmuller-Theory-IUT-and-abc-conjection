import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import Mathlib.Data.Real.Basic

/-!
  The source-facing initial Theta input used by Theorem 3.11.

  This small module deliberately contains only the opening arithmetic and
  place conditions.  The later procession, Kummer, and multiradial records
  live in `SourceFaithfulBoundary` and are not prerequisites for the H1/H2
  source conversion.
-/

namespace LeanFormal.IUT

noncomputable section

universe u

namespace Theorem311Source

structure InitialThetaInput (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData l
  selectedPlaces : Type u
  badPlaces : Type u
  badIncluded : badPlaces → selectedPlaces
  selectedNonempty : Nonempty selectedPlaces
  badFinite : Fintype badPlaces
  stableReduction : badPlaces → Prop
  stableReduction_proved : ∀ v, stableReduction v
  torsionImage : Prop
  torsionImage_proved : torsionImage
  cuspParameter : Real
  cusp_positive : 0 < cuspParameter

end Theorem311Source

end

end LeanFormal.IUT
