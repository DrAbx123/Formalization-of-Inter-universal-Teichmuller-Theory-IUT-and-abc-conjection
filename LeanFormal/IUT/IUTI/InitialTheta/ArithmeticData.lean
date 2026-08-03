import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.Arithmetic.FiniteLabels
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve

/-!
  Arithmetic input data for IUT I Definition 3.1.

  The fields use current Mathlib objects for prime numbers, number fields,
  finite-dimensional field towers, Galois extensions, and Weierstrass curves.
  The record is an explicit input interface: no theorem here claims that an
  arbitrary elliptic curve automatically satisfies the source's additional
  reduction, anabelian, or torsion hypotheses.
-/

namespace LeanFormal.IUT

universe u

def HasSqrtNegOne (F : Type u) [Field F] : Prop :=
  ∃ i : F, i * i = -1

structure ThetaFieldTower
    (l : PrimeGeFive) (Fmod F K : Type u)
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K] where
  sqrtNegOne : HasSqrtNegOne F
  degreePrimeToL : Nat.Coprime (Module.finrank Fmod F) l.value

namespace ThetaFieldTower

variable {l : PrimeGeFive} {Fmod F K : Type u}
  [Field Fmod] [NumberField Fmod]
  [Field F] [NumberField F]
  [Field K] [NumberField K]
  [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
  [IsScalarTower Fmod F K]
  [FiniteDimensional Fmod F] [IsGalois Fmod F]
  [FiniteDimensional F K] [IsGalois F K]
  (T : ThetaFieldTower l Fmod F K)

theorem sqrtNegOne_spec (T : ThetaFieldTower l Fmod F K) :
    HasSqrtNegOne F :=
  ThetaFieldTower.sqrtNegOne T

theorem degreePrimeToL_spec (T : ThetaFieldTower l Fmod F K) :
    Nat.Coprime (Module.finrank Fmod F) l.value :=
  ThetaFieldTower.degreePrimeToL T

theorem l_odd : Odd l.value := l.odd

end ThetaFieldTower

structure InitialThetaArithmeticData (l : PrimeGeFive) where
  Fmod : Type u
  [fieldFmod : Field Fmod]
  [numberFieldFmod : NumberField Fmod]
  F : Type u
  [fieldF : Field F]
  [numberFieldF : NumberField F]
  K : Type u
  [fieldK : Field K]
  [numberFieldK : NumberField K]
  [algebraFmodF : Algebra Fmod F]
  [algebraFK : Algebra F K]
  [algebraFmodK : Algebra Fmod K]
  [towerFmodFK : IsScalarTower Fmod F K]
  [finiteFmodF : FiniteDimensional Fmod F]
  [galoisFmodF : IsGalois Fmod F]
  [finiteFK : FiniteDimensional F K]
  [galoisFK : IsGalois F K]
  tower : ThetaFieldTower l Fmod F K
  curve : PuncturedEllipticCurve F

attribute [instance] InitialThetaArithmeticData.fieldFmod
  InitialThetaArithmeticData.numberFieldFmod
  InitialThetaArithmeticData.fieldF
  InitialThetaArithmeticData.numberFieldF
  InitialThetaArithmeticData.fieldK
  InitialThetaArithmeticData.numberFieldK
  InitialThetaArithmeticData.algebraFmodF
  InitialThetaArithmeticData.algebraFK
  InitialThetaArithmeticData.algebraFmodK
  InitialThetaArithmeticData.towerFmodFK
  InitialThetaArithmeticData.finiteFmodF
  InitialThetaArithmeticData.galoisFmodF
  InitialThetaArithmeticData.finiteFK
  InitialThetaArithmeticData.galoisFK

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def initialThetaArithmeticData : Obligation :=
  { id := "IUT-I.initial-theta-arithmetic-data"
    source := "IUT I, Definition 3.1 (arithmetic and elliptic-curve input)"
    status := VerificationStatus.interface
    note :=
      "Prime, number-field-tower, sqrt(-1), Galois/finite-dimensional, and " ++
        "Weierstrass-curve fields use Mathlib objects; existence and the " ++
        "remaining reduction/anabelian/torsion conditions are not proved."
    dependsOn := ["IUT-I.initial-theta-data"] }

end LeanFormal.IUT.Audit
