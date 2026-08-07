import LeanFormal.IUT.IUTI.InitialTheta.FinitePlaceInput

namespace LeanFormal.IUT

universe u

noncomputable section

structure InitialThetaSplitReductionInput (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData.{u} l
  place : NumberField.FinitePlace arithmetic.F
  qCandidate :
    NumberFieldFinitePlace.FinitePlaceQCandidate place
  splitReduction :
    arithmetic.curve.HasSplitMultiplicativeReductionAt place

namespace InitialThetaSplitReductionInput

variable {l : PrimeGeFive}

noncomputable def toFinitePlaceInput
    (input : InitialThetaSplitReductionInput.{u} l) :
    InitialThetaFinitePlaceInput l where
  arithmetic := input.arithmetic
  place := input.place
  qCandidate := input.qCandidate
  stableReduction :=
    PuncturedEllipticCurve.hasMultiplicativeReductionAt_imp_stable
      (PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_imp_multiplicative
        input.splitReduction)

theorem splitReduction_spec (input : InitialThetaSplitReductionInput.{u} l) :
    input.arithmetic.curve.HasSplitMultiplicativeReductionAt input.place :=
  input.splitReduction

theorem stableReduction (input : InitialThetaSplitReductionInput.{u} l) :
    input.arithmetic.curve.HasStableReductionAt input.place := by
  exact PuncturedEllipticCurve.hasMultiplicativeReductionAt_imp_stable
    (PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_imp_multiplicative
      input.splitReduction)

theorem toFinitePlaceInput_arithmetic
    (input : InitialThetaSplitReductionInput.{u} l) :
    input.toFinitePlaceInput.arithmetic = input.arithmetic :=
  rfl

theorem toFinitePlaceInput_place
    (input : InitialThetaSplitReductionInput.{u} l) :
    input.toFinitePlaceInput.place = input.place :=
  rfl

theorem toFinitePlaceInput_qCandidate
    (input : InitialThetaSplitReductionInput.{u} l) :
    input.toFinitePlaceInput.qCandidate = input.qCandidate :=
  rfl

theorem q_order_pos (input : InitialThetaSplitReductionInput.{u} l) :
    0 < input.qCandidate.order :=
  input.qCandidate.order_pos

theorem q_ne_one (input : InitialThetaSplitReductionInput.{u} l) :
    input.qCandidate.q ≠ 1 :=
  input.qCandidate.q_ne_one

theorem toFinitePlaceInput_q_order_pos
    (input : InitialThetaSplitReductionInput.{u} l) :
    0 < input.toFinitePlaceInput.qCandidate.order :=
  input.q_order_pos

theorem toFinitePlaceInput_q_ne_one
    (input : InitialThetaSplitReductionInput.{u} l) :
    input.toFinitePlaceInput.qCandidate.q ≠ 1 :=
  input.q_ne_one

theorem split_implies_stable
    (input : InitialThetaSplitReductionInput.{u} l) :
    input.arithmetic.curve.HasStableReductionAt input.place :=
  input.stableReduction

end InitialThetaSplitReductionInput

def InitialThetaSplitReductionInput.toStableReductionInput
    {l : PrimeGeFive} (input : InitialThetaSplitReductionInput.{u} l) :
    InitialThetaFinitePlaceInput l :=
  input.toFinitePlaceInput

structure InitialThetaReductionPlaceBoundary (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData.{u} l
  place : NumberField.FinitePlace arithmetic.F
  qCandidate :
    NumberFieldFinitePlace.FinitePlaceQCandidate place
  stableReduction : arithmetic.curve.HasStableReductionAt place
  splitReduction :
    arithmetic.curve.HasSplitMultiplicativeReductionAt place

namespace InitialThetaReductionPlaceBoundary

variable {l : PrimeGeFive}

def toSplitInput
    (boundary : InitialThetaReductionPlaceBoundary.{u} l) :
    InitialThetaSplitReductionInput l where
  arithmetic := boundary.arithmetic
  place := boundary.place
  qCandidate := boundary.qCandidate
  splitReduction := boundary.splitReduction

theorem toSplitInput_arithmetic
    (boundary : InitialThetaReductionPlaceBoundary.{u} l) :
    boundary.toSplitInput.arithmetic = boundary.arithmetic :=
  rfl

theorem toSplitInput_place
    (boundary : InitialThetaReductionPlaceBoundary.{u} l) :
    boundary.toSplitInput.place = boundary.place :=
  rfl

theorem toSplitInput_qCandidate
    (boundary : InitialThetaReductionPlaceBoundary.{u} l) :
    boundary.toSplitInput.qCandidate = boundary.qCandidate :=
  rfl

theorem toSplitInput_splitReduction
    (boundary : InitialThetaReductionPlaceBoundary.{u} l) :
    boundary.toSplitInput.arithmetic.curve.HasSplitMultiplicativeReductionAt
      boundary.toSplitInput.place :=
  boundary.splitReduction

theorem toSplitInput_stableReduction
    (boundary : InitialThetaReductionPlaceBoundary.{u} l) :
    boundary.toSplitInput.arithmetic.curve.HasStableReductionAt
      boundary.toSplitInput.place :=
  boundary.toSplitInput.stableReduction

def toFinitePlaceInput
    (boundary : InitialThetaReductionPlaceBoundary.{u} l) :
    InitialThetaFinitePlaceInput l :=
  boundary.toSplitInput.toFinitePlaceInput

theorem toFinitePlaceInput_arithmetic
    (boundary : InitialThetaReductionPlaceBoundary.{u} l) :
    boundary.toFinitePlaceInput.arithmetic = boundary.arithmetic :=
  rfl

theorem toFinitePlaceInput_place
    (boundary : InitialThetaReductionPlaceBoundary.{u} l) :
    boundary.toFinitePlaceInput.place = boundary.place :=
  rfl

theorem toFinitePlaceInput_qCandidate
    (boundary : InitialThetaReductionPlaceBoundary.{u} l) :
    boundary.toFinitePlaceInput.qCandidate = boundary.qCandidate :=
  rfl

theorem toFinitePlaceInput_stableReduction
    (boundary : InitialThetaReductionPlaceBoundary.{u} l) :
    boundary.toFinitePlaceInput.arithmetic.curve.HasStableReductionAt
      boundary.toFinitePlaceInput.place :=
  boundary.toSplitInput.toFinitePlaceInput.stableReduction

end InitialThetaReductionPlaceBoundary

structure InitialThetaSplitReductionFamily (l : PrimeGeFive) where
  index : Type u
  [indexFintype : Fintype index]
  input : index → InitialThetaSplitReductionInput.{u} l
  sameArithmetic : ∀ i j, (input i).arithmetic = (input j).arithmetic

attribute [instance] InitialThetaSplitReductionFamily.indexFintype

namespace InitialThetaSplitReductionFamily

variable {l : PrimeGeFive}

theorem input_splitReduction
    (family : InitialThetaSplitReductionFamily.{u} l) (i : family.index) :
    (family.input i).arithmetic.curve.HasSplitMultiplicativeReductionAt
      (family.input i).place :=
  (family.input i).splitReduction

theorem input_stableReduction
    (family : InitialThetaSplitReductionFamily.{u} l) (i : family.index) :
    (family.input i).arithmetic.curve.HasStableReductionAt
      (family.input i).place :=
  (family.input i).stableReduction

theorem input_q_order_pos
    (family : InitialThetaSplitReductionFamily.{u} l) (i : family.index) :
    0 < (family.input i).qCandidate.order :=
  (family.input i).q_order_pos

theorem input_q_ne_one
    (family : InitialThetaSplitReductionFamily.{u} l) (i : family.index) :
    (family.input i).qCandidate.q ≠ 1 :=
  (family.input i).q_ne_one

def toFinitePlaceInput
    (family : InitialThetaSplitReductionFamily.{u} l) (i : family.index) :
    InitialThetaFinitePlaceInput l :=
  (family.input i).toFinitePlaceInput

theorem toFinitePlaceInput_stableReduction
    (family : InitialThetaSplitReductionFamily.{u} l) (i : family.index) :
    (family.toFinitePlaceInput i).arithmetic.curve.HasStableReductionAt
      (family.toFinitePlaceInput i).place :=
  (family.input i).stableReduction

theorem same_arithmetic
    (family : InitialThetaSplitReductionFamily.{u} l)
    (i j : family.index) :
    (family.input i).arithmetic = (family.input j).arithmetic :=
  family.sameArithmetic i j

end InitialThetaSplitReductionFamily

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def initialThetaSplitReductionInput : Obligation :=
  { id := "IUT-I.initial-theta-split-reduction-input"
    source := "IUT I, Definition 3.1(b); split multiplicative selected place"
    status := VerificationStatus.interface
    note :=
      "The split-multiplicative place boundary is a concrete typed input. " ++
        "Its stable-reduction projection and q-candidate consequences are " ++
        "proved. Existence of such a place for the selected arithmetic curve, " ++
        "and its Tate/source-anabelian realization, remain open obligations."
    dependsOn :=
      [ "IUT-I.initial-theta-finite-place-input",
        "Foundations.Geometry.elliptic-local-reduction" ] }

end LeanFormal.IUT.Audit
