/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import Iut.Foundations.Orbicurve

/-!
  A source-faithful rank-one quotient of the actual l-torsion module.

  The quotient in IUT I, Definition 3.1(c), is a quotient of the l-torsion
  module onto a free rank-one `ZMod l`-module.  This file constructs the
  quotient from an explicitly supplied torsion basis.  Its source carrier is
  the actual algebraic-closure torsion module; no field element or cusp is
  silently substituted for the quotient.

  The further identification with `E_K[l]` and the construction of the cusp
  require separate descent and boundary comparison theorems.  They are not
  asserted here.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

namespace InitialThetaSource

structure TorsionRankOneQuotientData (l : PrimeGeFive)
    (A : InitialThetaArithmeticData l) where
  torsion_basis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l

namespace TorsionRankOneQuotientData

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

abbrev Torsion (D : TorsionRankOneQuotientData l A) :=
  A.curve.LTorsion l

abbrev Scalar (D : TorsionRankOneQuotientData l A) :=
  ZMod l.value

def quotientMap (D : TorsionRankOneQuotientData l A) :
    D.Torsion →ₗ[D.Scalar] D.Scalar :=
  (LinearMap.proj (R := D.Scalar) 0).comp D.torsion_basis.symm

theorem quotientMap_surjective (D : TorsionRankOneQuotientData l A) :
    Function.Surjective D.quotientMap := by
  exact
    (LinearMap.proj_surjective (R := D.Scalar) 0).comp
      D.torsion_basis.symm.surjective

abbrev Kernel (D : TorsionRankOneQuotientData l A) :=
  LinearMap.ker D.quotientMap

abbrev Quotient (D : TorsionRankOneQuotientData l A) :=
  D.Torsion ⧸ D.Kernel

noncomputable def quotientEquiv (D : TorsionRankOneQuotientData l A) :
    D.Quotient ≃ₗ[D.Scalar] D.Scalar :=
  D.quotientMap.quotKerEquivOfSurjective D.quotientMap_surjective

def standardCoordinate : Fin 2 → ZMod l.value :=
  fun i => if i = 0 then 1 else 0

def distinguishedClass (D : TorsionRankOneQuotientData l A) : D.Quotient :=
  D.Kernel.mkQ (D.torsion_basis D.standardCoordinate)

theorem quotientMap_basis_standard (D : TorsionRankOneQuotientData l A) :
    D.quotientMap (D.torsion_basis D.standardCoordinate) = 1 := by
  simp [quotientMap, standardCoordinate]

theorem quotientEquiv_distinguished (D : TorsionRankOneQuotientData l A) :
    D.quotientEquiv D.distinguishedClass = 1 := by
  simp [distinguishedClass, quotientEquiv, quotientMap,
    standardCoordinate]

theorem distinguishedClass_nonzero (D : TorsionRankOneQuotientData l A) :
    D.distinguishedClass ≠ 0 := by
  intro h
  have h' := congrArg D.quotientEquiv h
  rw [D.quotientEquiv_distinguished] at h'
  simpa using h'

theorem quotient_is_rank_one (D : TorsionRankOneQuotientData l A) :
    Nonempty (D.Quotient ≃ₗ[D.Scalar] D.Scalar) :=
  ⟨D.quotientEquiv⟩

theorem source_rank_one_quotient_spec
    (D : TorsionRankOneQuotientData l A) :
    Function.Surjective D.quotientMap ∧
      D.distinguishedClass ≠ 0 ∧
      D.quotientEquiv D.distinguishedClass = 1 :=
  ⟨D.quotientMap_surjective, D.distinguishedClass_nonzero,
    D.quotientEquiv_distinguished⟩

end TorsionRankOneQuotientData

/-!
  A boundary origin is part of the source datum, rather than a later
  proposition about an unrelated field element.  Its domain is the actual
  nonzero quotient of the algebraic-closure `l`-torsion module, and its
  selected class and cusp are tied by one actual origin map.
-/
structure TorsionQuotientBoundaryOrigin (l : PrimeGeFive)
    (A : InitialThetaArithmeticData l)
    (X : Iut.HyperbolicOrbicurve A.K) where
  rank_one_quotient : TorsionRankOneQuotientData l A
  originMap :
    {q : rank_one_quotient.Quotient // q ≠ 0} →
      Iut.OrbicurveBoundaryCusp X
  cusp : Iut.OrbicurveBoundaryCusp X
  originMap_distinguishedClass :
    originMap
        ⟨rank_one_quotient.distinguishedClass,
          rank_one_quotient.distinguishedClass_nonzero⟩ = cusp

namespace TorsionQuotientBoundaryOrigin

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {X : Iut.HyperbolicOrbicurve A.K}

abbrev Quotient (O : TorsionQuotientBoundaryOrigin l A X) :=
  O.rank_one_quotient.Quotient

abbrev NonzeroClass (O : TorsionQuotientBoundaryOrigin l A X) :=
  {q : O.Quotient // q ≠ 0}

noncomputable def distinguishedNonzeroClass
    (O : TorsionQuotientBoundaryOrigin l A X) : O.NonzeroClass :=
  ⟨O.rank_one_quotient.distinguishedClass,
    O.rank_one_quotient.distinguishedClass_nonzero⟩

theorem nonzeroClass_ne_zero
    (O : TorsionQuotientBoundaryOrigin l A X) :
    (O.distinguishedNonzeroClass : O.Quotient) ≠ 0 :=
  O.distinguishedNonzeroClass.property

theorem originMap_nonzeroClass_spec
    (O : TorsionQuotientBoundaryOrigin l A X) :
    O.originMap O.distinguishedNonzeroClass = O.cusp := by
  simpa [distinguishedNonzeroClass] using O.originMap_distinguishedClass

theorem quotientMap_surjective
    (O : TorsionQuotientBoundaryOrigin l A X) :
    Function.Surjective O.rank_one_quotient.quotientMap :=
  O.rank_one_quotient.quotientMap_surjective

theorem distinguishedClass_nonzero
    (O : TorsionQuotientBoundaryOrigin l A X) :
    O.rank_one_quotient.distinguishedClass ≠ 0 :=
  O.rank_one_quotient.distinguishedClass_nonzero

theorem distinguishedClass_is_generator
    (O : TorsionQuotientBoundaryOrigin l A X) :
    O.rank_one_quotient.quotientEquiv
        O.rank_one_quotient.distinguishedClass = 1 :=
  O.rank_one_quotient.quotientEquiv_distinguished

theorem nonzero_origin_spec
    (O : TorsionQuotientBoundaryOrigin l A X) :
    ∃ q : O.Quotient, q ≠ 0 :=
  ⟨O.distinguishedNonzeroClass, O.nonzeroClass_ne_zero⟩

theorem source_rank_one_boundary_origin_spec
    (O : TorsionQuotientBoundaryOrigin l A X) :
    Function.Surjective O.rank_one_quotient.quotientMap ∧
      O.rank_one_quotient.distinguishedClass ≠ 0 ∧
      O.rank_one_quotient.quotientEquiv
          O.rank_one_quotient.distinguishedClass = 1 ∧
      O.originMap O.distinguishedNonzeroClass = O.cusp :=
  ⟨O.quotientMap_surjective, O.distinguishedClass_nonzero,
    O.distinguishedClass_is_generator, O.originMap_nonzeroClass_spec⟩

end TorsionQuotientBoundaryOrigin

end InitialThetaSource

end

end LeanFormal.IUT
