/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion

/-!
  # Binding the geometric sign-quotient core to the selected places

  The source tuple contains two logically different pieces of data.  The
  geometric part consists of the represented orbicurves, the sign action and
  quotient, the finite-etale fundamental-group data, the scalar extensions,
  and the boundary cusp.  The place part consists of the moduli bad-place set
  and the restriction section selecting places upstairs.

  `SourceSignQuotientGeometricCore` separates these pieces so that the place
  fields cannot be copied from a second source record.  Its constructor below
  uses the actual `SourcePlaceSelection` section and transports every selected
  place field by definitional equality.  This is a construction from supplied
  source objects; it is not a construction from `InitialThetaArithmeticData`.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

namespace InitialThetaSource

/-! The source geometry and group data, with the place fields factored out. -/
structure SourceSignQuotientGeometricCore
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l) where
  xF : Iut.HyperbolicOrbicurve A.F
  xF_geometry : SourceOncePuncturedGeometry A.curve xF
  ellipticInvolution : xF.Hom xF
  ellipticInvolution_squared :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp ellipticInvolution ellipticInvolution)
      (Iut.HyperbolicOrbicurve.Hom.id xF)
  unique_elliptic_involution :
    ∀ inv : xF.Hom xF,
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id xF) →
      inv = ellipticInvolution
  signAction : Iut.OrbicurveSignAction xF
  signAction_inversion_eq_ellipticInvolution :
    signAction.inversion = ellipticInvolution
  cF : Iut.HyperbolicOrbicurve A.F
  quotient : Iut.OrbicurveSignInvariantMorphism signAction cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient
  xFGroups : SourceOrbicurveGroupData xF (Iut.AbsoluteGaloisProfinite A.F)
  cFGroups : SourceOrbicurveGroupData cF (Iut.AbsoluteGaloisProfinite A.F)
  fGroupInclusion : Iut.ProfiniteFundamentalGroupInclusion
    xFGroups.sequence.geometric xFGroups.sequence.arithmetic
    cFGroups.sequence.geometric cFGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite A.F)
    xFGroups.sequence cFGroups.sequence
  xK : Iut.HyperbolicOrbicurve A.K
  cK : Iut.HyperbolicOrbicurve A.K
  xKExtension : SourceOrbicurveScalarExtension A.F A.K xF
  cKExtension : SourceOrbicurveScalarExtension A.F A.K cF
  xKType : xK.signature = sourceTypeOneLTorsion l
  cKType : cK.signature = sourceTypeOneLTorsionPlusMinus l
  xK_eq_extension : xK = xKExtension.result
  cK_eq_extension : cK = cKExtension.result
  epsilon : Iut.OrbicurveBoundaryCusp cK

namespace SourceSignQuotientGeometricCore

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}

/-! The exact source package obtained after applying one actual place section. -/
noncomputable def toSourceCompletionSignQuotient
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    SourceCompletionSignQuotient A where
  xF := G.xF
  xF_geometry := G.xF_geometry
  ellipticInvolution := G.ellipticInvolution
  ellipticInvolution_squared := G.ellipticInvolution_squared
  unique_elliptic_involution := G.unique_elliptic_involution
  signAction := G.signAction
  signAction_inversion_eq_ellipticInvolution :=
    G.signAction_inversion_eq_ellipticInvolution
  cF := G.cF
  quotient := G.quotient
  quotientWitness := G.quotientWitness
  xFGroups := G.xFGroups
  cFGroups := G.cFGroups
  fGroupInclusion := G.fGroupInclusion
  xK := G.xK
  cK := G.cK
  xKExtension := G.xKExtension
  cKExtension := G.cKExtension
  xKType := G.xKType
  cKType := G.cKType
  xK_eq_extension := G.xK_eq_extension
  cK_eq_extension := G.cK_eq_extension
  V := P.V
  V_mod_bad := P.V_mod_bad
  V_mod_bad_odd_residue_characteristic :=
    P.V_mod_bad_odd_residue_characteristic
  V_mod_bad_nonempty := P.V_mod_bad_nonempty
  V_section := P.V_section
  V_eq_section := P.V_eq_section
  V_mod_bijection := P.V_mod_bijection
  V_place_comap := P.V_place_comap
  epsilon := G.epsilon

@[simp] theorem toSourceCompletionSignQuotient_xF
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceCompletionSignQuotient P).xF = G.xF :=
  rfl

@[simp] theorem toSourceCompletionSignQuotient_cF
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceCompletionSignQuotient P).cF = G.cF :=
  rfl

@[simp] theorem toSourceCompletionSignQuotient_xK
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceCompletionSignQuotient P).xK = G.xK :=
  rfl

@[simp] theorem toSourceCompletionSignQuotient_cK
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceCompletionSignQuotient P).cK = G.cK :=
  rfl

@[simp] theorem toSourceCompletionSignQuotient_V
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceCompletionSignQuotient P).V = P.V :=
  rfl

@[simp] theorem toSourceCompletionSignQuotient_V_mod_bad
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceCompletionSignQuotient P).V_mod_bad = P.V_mod_bad :=
  rfl

@[simp] theorem toSourceCompletionSignQuotient_V_section
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceCompletionSignQuotient P).V_section = P.V_section :=
  rfl

@[simp] theorem toSourceCompletionSignQuotient_V_mod_bijection
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceCompletionSignQuotient P).V_mod_bijection =
      P.V_mod_bijection :=
  rfl

@[simp] theorem toSourceCompletionSignQuotient_epsilon
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceCompletionSignQuotient P).epsilon = G.epsilon :=
  rfl

theorem toSourceCompletionSignQuotient_selected_places
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceCompletionSignQuotient P).V =
      (G.toSourceCompletionSignQuotient P).V_section.selected :=
  P.V_eq_section

theorem toSourceCompletionSignQuotient_bad_nonempty
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceCompletionSignQuotient P).V_mod_bad.Nonempty :=
  P.V_mod_bad_nonempty

theorem toSourceCompletionSignQuotient_bad_odd
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod)
    (hp : p ∈ (G.toSourceCompletionSignQuotient P).V_mod_bad) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  P.V_mod_bad_odd_residue_characteristic p hp

theorem toSourceCompletionSignQuotient_place_comap
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (v : {v : NumberFieldPlace A.K //
      v ∈ (G.toSourceCompletionSignQuotient P).V}) :
    NumberFieldPlace.comap (k := A.Fmod) v.1 =
      (G.toSourceCompletionSignQuotient P).V_mod_bijection.symm v :=
  P.V_place_comap v

noncomputable def toSourceSignQuotientData
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    SourceSignQuotientData A :=
  (G.toSourceCompletionSignQuotient P).toSourceSignQuotientData

@[simp] theorem toSourceSignQuotientData_xF
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceSignQuotientData P).xF = G.xF :=
  rfl

@[simp] theorem toSourceSignQuotientData_cK
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceSignQuotientData P).cK = G.cK :=
  rfl

@[simp] theorem toSourceSignQuotientData_V
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceSignQuotientData P).V = P.V :=
  rfl

@[simp] theorem toSourceSignQuotientData_V_mod_bad
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceSignQuotientData P).V_mod_bad = P.V_mod_bad :=
  rfl

@[simp] theorem toSourceSignQuotientData_epsilon
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceSignQuotientData P).epsilon = G.epsilon :=
  rfl

theorem toSourceSignQuotientData_selected_places
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A) :
    (G.toSourceSignQuotientData P).V =
      (G.toSourceSignQuotientData P).V_section.selected :=
  P.V_eq_section

theorem toSourceSignQuotientData_place_comap
    (G : SourceSignQuotientGeometricCore A)
    (P : SourcePlaceSelection A)
    (v : {v : NumberFieldPlace A.K //
      v ∈ (G.toSourceSignQuotientData P).V}) :
    NumberFieldPlace.comap (k := A.Fmod) v.1 =
      (G.toSourceSignQuotientData P).V_mod_bijection.symm v :=
  P.V_place_comap v

end SourceSignQuotientGeometricCore

end InitialThetaSource

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def initialThetaSourceSignQuotientConstruction : Obligation :=
  { id := "IUT-I.definition-3.1-A2-sign-quotient-place-binding"
    source := "IUT I, Definition 3.1(e)-(f) and place notation"
    status := VerificationStatus.interface
    note :=
      "A supplied geometric sign-quotient core and a supplied bad-place " ++
        "selection are assembled into one dependent SourceSignQuotientData. " ++
        "The selected set, restriction section, place equivalence, comap " ++
        "identity, odd residue characteristic, and cusp are copied from the " ++
        "same source inputs. This does not construct the geometric core, the " ++
        "bad-place reduction, or the cusp from arithmetic data."
    dependsOn :=
      [ "IUT-I.definition-3.1-A2-quantifier-boundary",
        "IUT-I.initial-theta-place-selection" ] }

end LeanFormal.IUT.Audit
