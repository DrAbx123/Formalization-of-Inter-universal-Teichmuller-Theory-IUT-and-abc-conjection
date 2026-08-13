import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.Audit.Status
import Mathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
  # Definition 3.1 D2: the arithmetic root output

  `InitialThetaArithmeticData` is the arithmetic input allowed at the opening
  of Definition 3.1.  Its fields already contain the number-field tower, the
  finite-dimensional/Galois instances, the square root of `-1`, and the
  elliptic-curve carrier.  This module exposes those fields as a small,
  reusable root object with named recovery theorems.

  The module does not construct bad places, reductions, torsion images,
  orbicurves, sections, or cusp data.  Those are later Definition 3.1
  clauses and remain separate source obligations.  In particular, every
  theorem below is universally quantified over the supplied arithmetic input;
  no new hypothesis is introduced and no source conclusion is stored as an
  input field.

  Source: IUT I, Definition 3.1, the arithmetic tower and elliptic-curve
  clauses.
-/

namespace LeanFormal.IUT

noncomputable section

universe u

namespace InitialThetaSource
namespace Definition31D2Root

variable {l : PrimeGeFive}

/-! ## D2 output and canonical constructor -/

structure Output (A : InitialThetaArithmeticData.{u} l) where
  tower : ThetaFieldTower l A.Fmod A.F A.K
  curve : PuncturedEllipticCurve A.F
  sqrtNegOne : HasSqrtNegOne A.F
  degreePrimeToL : Nat.Coprime (Module.finrank A.Fmod A.F) l.value

def ofArithmetic (A : InitialThetaArithmeticData.{u} l) : Output A where
  tower := A.tower
  curve := A.curve
  sqrtNegOne := A.tower.sqrtNegOne
  degreePrimeToL := A.tower.degreePrimeToL

@[simp] theorem tower_recovery (A : InitialThetaArithmeticData.{u} l) :
    (ofArithmetic A).tower = A.tower := rfl

@[simp] theorem curve_recovery (A : InitialThetaArithmeticData.{u} l) :
    (ofArithmetic A).curve = A.curve := rfl

theorem sqrtNegOne_recovery (A : InitialThetaArithmeticData.{u} l) :
    (ofArithmetic A).sqrtNegOne = A.tower.sqrtNegOne := rfl

theorem degreePrimeToL_recovery (A : InitialThetaArithmeticData.{u} l) :
    (ofArithmetic A).degreePrimeToL = A.tower.degreePrimeToL := rfl

theorem sqrtNegOne_spec (A : InitialThetaArithmeticData.{u} l) :
    HasSqrtNegOne A.F :=
  (ofArithmetic A).sqrtNegOne

theorem degreePrimeToL_spec (A : InitialThetaArithmeticData.{u} l) :
    Nat.Coprime (Module.finrank A.Fmod A.F) l.value :=
  (ofArithmetic A).degreePrimeToL

def curve_spec (A : InitialThetaArithmeticData.{u} l) :
    PuncturedEllipticCurve A.F :=
  (ofArithmetic A).curve

/-! ## D2 carrier instances -/

@[reducible] def field_fmod (A : InitialThetaArithmeticData.{u} l) :
    Field A.Fmod := by
  infer_instance

theorem numberField_fmod (A : InitialThetaArithmeticData.{u} l) :
    NumberField A.Fmod := by
  infer_instance

@[reducible] def field_f (A : InitialThetaArithmeticData.{u} l) :
    Field A.F := by
  infer_instance

theorem numberField_f (A : InitialThetaArithmeticData.{u} l) :
    NumberField A.F := by
  infer_instance

@[reducible] def field_k (A : InitialThetaArithmeticData.{u} l) :
    Field A.K := by
  infer_instance

theorem numberField_k (A : InitialThetaArithmeticData.{u} l) :
    NumberField A.K := by
  infer_instance

@[reducible] def algebra_fmod_f (A : InitialThetaArithmeticData.{u} l) :
    Algebra A.Fmod A.F := by
  infer_instance

@[reducible] def algebra_f_k (A : InitialThetaArithmeticData.{u} l) :
    Algebra A.F A.K := by
  infer_instance

@[reducible] def algebra_fmod_k (A : InitialThetaArithmeticData.{u} l) :
    Algebra A.Fmod A.K := by
  infer_instance

theorem scalar_tower_fmod_f_k (A : InitialThetaArithmeticData.{u} l) :
    IsScalarTower A.Fmod A.F A.K := by
  infer_instance

theorem finiteDimensional_fmod_f (A : InitialThetaArithmeticData.{u} l) :
    FiniteDimensional A.Fmod A.F := by
  infer_instance

theorem finiteDimensional_f_k (A : InitialThetaArithmeticData.{u} l) :
    FiniteDimensional A.F A.K := by
  infer_instance

theorem isGalois_fmod_f (A : InitialThetaArithmeticData.{u} l) :
    IsGalois A.Fmod A.F := by
  infer_instance

theorem isGalois_f_k (A : InitialThetaArithmeticData.{u} l) :
    IsGalois A.F A.K := by
  infer_instance

theorem number_field_instances (A : InitialThetaArithmeticData.{u} l) :
    NumberField A.Fmod ∧ NumberField A.F ∧ NumberField A.K := by
  exact ⟨numberField_fmod A, numberField_f A, numberField_k A⟩

theorem finite_galois_instances (A : InitialThetaArithmeticData.{u} l) :
    FiniteDimensional A.Fmod A.F ∧
      FiniteDimensional A.F A.K ∧
      IsGalois A.Fmod A.F ∧
      IsGalois A.F A.K := by
  exact ⟨finiteDimensional_fmod_f A, finiteDimensional_f_k A,
    isGalois_fmod_f A, isGalois_f_k A⟩

/-! ## D2 theorem-facing projections -/

theorem arithmetic_tower_is_source_tower
    (A : InitialThetaArithmeticData.{u} l) :
    (ofArithmetic A).tower = A.tower :=
  tower_recovery A

theorem arithmetic_curve_is_source_curve
    (A : InitialThetaArithmeticData.{u} l) :
    (ofArithmetic A).curve = A.curve :=
  curve_recovery A

theorem arithmetic_sqrt_neg_one
    (A : InitialThetaArithmeticData.{u} l) :
    ∃ i : A.F, i * i = -1 := by
  exact sqrtNegOne_spec A

theorem arithmetic_finrank_coprime_l
    (A : InitialThetaArithmeticData.{u} l) :
    Nat.Coprime (Module.finrank A.Fmod A.F) l.value :=
  degreePrimeToL_spec A

theorem arithmetic_l_odd (A : InitialThetaArithmeticData.{u} l) :
    Odd l.value :=
  l.odd

theorem arithmetic_l_ge_five (A : InitialThetaArithmeticData.{u} l) :
    5 ≤ l.value :=
  l.ge_five

theorem arithmetic_l_ne_zero (A : InitialThetaArithmeticData.{u} l) :
    l.value ≠ 0 :=
  by
    have hl := l.ge_five
    omega

theorem arithmetic_tower_pair
    (A : InitialThetaArithmeticData.{u} l) :
    HasSqrtNegOne A.F ∧
      Nat.Coprime (Module.finrank A.Fmod A.F) l.value :=
  ⟨sqrtNegOne_spec A, degreePrimeToL_spec A⟩

theorem arithmetic_carrier_pair
    (A : InitialThetaArithmeticData.{u} l) :
    (ofArithmetic A).tower = A.tower ∧
      (ofArithmetic A).curve = A.curve :=
  ⟨tower_recovery A, curve_recovery A⟩

theorem arithmetic_root_closed
    (A : InitialThetaArithmeticData.{u} l) :
    HasSqrtNegOne A.F ∧
      Nat.Coprime (Module.finrank A.Fmod A.F) l.value :=
  ⟨sqrtNegOne_spec A, degreePrimeToL_spec A⟩

/-! A compact record is useful when the next source layer consumes D2. -/

structure CarrierSummary (A : InitialThetaArithmeticData.{u} l) where
  tower : ThetaFieldTower l A.Fmod A.F A.K
  curve : PuncturedEllipticCurve A.F

def carrierSummary (A : InitialThetaArithmeticData.{u} l) :
    CarrierSummary A where
  tower := A.tower
  curve := A.curve

theorem carrierSummary_tower (A : InitialThetaArithmeticData.{u} l) :
    (carrierSummary A).tower = A.tower := rfl

theorem carrierSummary_curve (A : InitialThetaArithmeticData.{u} l) :
    (carrierSummary A).curve = A.curve := rfl

theorem carrierSummary_recovered
    (A : InitialThetaArithmeticData.{u} l) :
    (carrierSummary A).tower = A.tower ∧
      (carrierSummary A).curve = A.curve := by
  exact ⟨carrierSummary_tower A, carrierSummary_curve A⟩

/-! ## D2 status marker -/

theorem d2_root_status : True := by
  trivial

end Definition31D2Root
end InitialThetaSource

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def theorem311D2ArithmeticRoot : Obligation :=
  { id := "IUT-I.definition-3.1-D2-arithmetic-root"
    source := "IUT I, Definition 3.1 (arithmetic tower and curve clauses)"
    status := VerificationStatus.proved
    note :=
      "For every supplied InitialThetaArithmeticData, the tower, curve, " ++
        "sqrt(-1), finite-dimensional/Galois instances, and finrank/l " ++
        "coprimality are exposed by Definition31D2Root. This closes only " ++
        "the arithmetic root projection; places, reductions, torsion, " ++
        "orbicurves, sections, and cusp clauses remain separate obligations."
    dependsOn := ["IUT-I.initial-theta-arithmetic-data"] }

end LeanFormal.IUT.Audit
