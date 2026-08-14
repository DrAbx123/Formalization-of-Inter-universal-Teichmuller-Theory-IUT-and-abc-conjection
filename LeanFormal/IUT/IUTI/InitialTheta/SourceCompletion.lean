/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourceArithmeticPrelude

/-!
  # Explicit source completion for IUT I Definition 3.1

  `InitialThetaArithmeticData` contains the number-field tower and the
  punctured elliptic curve only.  The paper's initial Theta-data additionally
  contains the represented orbicurves, their finite-etale fundamental-group
  data, reduction and Tate comparisons, torsion/Galois data, local sections,
  and the quotient-origin cusp.  `SourceCompletion` is the explicit witness
  package for those objects.  Its `arithmeticPrelude` is constructed from the
  actual algebraic closure, place section, and K/F torsion transport; the
  remaining source fields are deliberately not constructed from an
  arbitrary arithmetic record: no theorem in this file turns a missing source
  condition into a witness.

  The assembly theorem below is therefore a genuine implication
  `SourceCompletion -> SourceNativeInitialThetaData`.  The separate universal
  proposition `SourceNativeArithmeticToSourceGate` remains untouched.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

namespace InitialThetaSource

/-! The first stage is written field-by-field so the construction of
    `SourceSignQuotientData` remains visible.  Every field is one of the
    source-facing records from `SourceDefinition31Quantifiers`; no
    unconstrained carrier is introduced. -/
structure SourceCompletionSignQuotient
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
  V : Set (NumberFieldPlace A.K)
  V_mod_bad : Set (NumberField.FinitePlace A.Fmod)
  V_mod_bad_odd_residue_characteristic :
    ∀ p, p ∈ V_mod_bad →
      Odd (NumberFieldFinitePlace.residueCharacteristic p)
  V_mod_bad_nonempty : V_mod_bad.Nonempty
  V_section : NumberFieldPlace.RestrictionSection A.Fmod A.K
  V_eq_section : V = V_section.selected
  V_mod_bijection :
    NumberFieldPlace A.Fmod ≃ {v : NumberFieldPlace A.K // v ∈ V}
  V_place_comap :
    ∀ v : {v : NumberFieldPlace A.K // v ∈ V},
      NumberFieldPlace.comap (k := A.Fmod) v.1 = V_mod_bijection.symm v
  epsilon : Iut.OrbicurveBoundaryCusp cK

namespace SourceCompletionSignQuotient

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData l}

/-!
  Rebind only the selected-place fields of an already supplied sign-quotient
  witness.  The hypothesis identifies the same bad-place set; the new selected
  set is the image of the actual restriction section.  Every geometric and
  group field is copied from the original witness, so this adapter cannot
  silently change the source curve or its cusp.
-/
noncomputable def withCanonicalPlaceSection
    (R : SourceCompletionSignQuotient A)
    (P : SourcePlaceSelection A)
    (hbad : P.V_mod_bad = R.V_mod_bad) :
    SourceCompletionSignQuotient A where
  xF := R.xF
  xF_geometry := R.xF_geometry
  ellipticInvolution := R.ellipticInvolution
  ellipticInvolution_squared := R.ellipticInvolution_squared
  unique_elliptic_involution := R.unique_elliptic_involution
  signAction := R.signAction
  signAction_inversion_eq_ellipticInvolution :=
    R.signAction_inversion_eq_ellipticInvolution
  cF := R.cF
  quotient := R.quotient
  quotientWitness := R.quotientWitness
  xFGroups := R.xFGroups
  cFGroups := R.cFGroups
  fGroupInclusion := R.fGroupInclusion
  xK := R.xK
  cK := R.cK
  xKExtension := R.xKExtension
  cKExtension := R.cKExtension
  xKType := R.xKType
  cKType := R.cKType
  xK_eq_extension := R.xK_eq_extension
  cK_eq_extension := R.cK_eq_extension
  V := P.V
  V_mod_bad := P.V_mod_bad
  V_mod_bad_odd_residue_characteristic := by
    intro p hp
    exact R.V_mod_bad_odd_residue_characteristic p (hbad ▸ hp)
  V_mod_bad_nonempty := by
    exact hbad.symm ▸ R.V_mod_bad_nonempty
  V_section := P.V_section
  V_eq_section := P.V_eq_section
  V_mod_bijection := P.V_mod_bijection
  V_place_comap := P.V_place_comap
  epsilon := R.epsilon

@[simp] theorem withCanonicalPlaceSection_xF
    (R : SourceCompletionSignQuotient A)
    (P : SourcePlaceSelection A)
    (hbad : P.V_mod_bad = R.V_mod_bad) :
    (withCanonicalPlaceSection R P hbad).xF = R.xF :=
  rfl

@[simp] theorem withCanonicalPlaceSection_cF
    (R : SourceCompletionSignQuotient A)
    (P : SourcePlaceSelection A)
    (hbad : P.V_mod_bad = R.V_mod_bad) :
    (withCanonicalPlaceSection R P hbad).cF = R.cF :=
  rfl

@[simp] theorem withCanonicalPlaceSection_xK
    (R : SourceCompletionSignQuotient A)
    (P : SourcePlaceSelection A)
    (hbad : P.V_mod_bad = R.V_mod_bad) :
    (withCanonicalPlaceSection R P hbad).xK = R.xK :=
  rfl

@[simp] theorem withCanonicalPlaceSection_cK
    (R : SourceCompletionSignQuotient A)
    (P : SourcePlaceSelection A)
    (hbad : P.V_mod_bad = R.V_mod_bad) :
    (withCanonicalPlaceSection R P hbad).cK = R.cK :=
  rfl

@[simp] theorem withCanonicalPlaceSection_V
    (R : SourceCompletionSignQuotient A)
    (P : SourcePlaceSelection A)
    (hbad : P.V_mod_bad = R.V_mod_bad) :
    (withCanonicalPlaceSection R P hbad).V = P.V :=
  rfl

@[simp] theorem withCanonicalPlaceSection_V_mod_bad
    (R : SourceCompletionSignQuotient A)
    (P : SourcePlaceSelection A)
    (hbad : P.V_mod_bad = R.V_mod_bad) :
    (withCanonicalPlaceSection R P hbad).V_mod_bad = P.V_mod_bad :=
  rfl

@[simp] theorem withCanonicalPlaceSection_V_section
    (R : SourceCompletionSignQuotient A)
    (P : SourcePlaceSelection A)
    (hbad : P.V_mod_bad = R.V_mod_bad) :
    (withCanonicalPlaceSection R P hbad).V_section = P.V_section :=
  rfl

@[simp] theorem withCanonicalPlaceSection_V_mod_bijection
    (R : SourceCompletionSignQuotient A)
    (P : SourcePlaceSelection A)
    (hbad : P.V_mod_bad = R.V_mod_bad) :
    (withCanonicalPlaceSection R P hbad).V_mod_bijection =
      P.V_mod_bijection :=
  rfl

@[simp] theorem withCanonicalPlaceSection_epsilon
    (R : SourceCompletionSignQuotient A)
    (P : SourcePlaceSelection A)
    (hbad : P.V_mod_bad = R.V_mod_bad) :
    (withCanonicalPlaceSection R P hbad).epsilon = R.epsilon :=
  rfl

theorem withCanonicalPlaceSection_selected_places
    (R : SourceCompletionSignQuotient A)
    (P : SourcePlaceSelection A)
    (hbad : P.V_mod_bad = R.V_mod_bad) :
    (withCanonicalPlaceSection R P hbad).V =
      (withCanonicalPlaceSection R P hbad).V_section.selected :=
  (withCanonicalPlaceSection R P hbad).V_eq_section

theorem withCanonicalPlaceSection_place_comap
    (R : SourceCompletionSignQuotient A)
    (P : SourcePlaceSelection A)
    (hbad : P.V_mod_bad = R.V_mod_bad)
    (v : {v : NumberFieldPlace A.K //
      v ∈ (withCanonicalPlaceSection R P hbad).V}) :
    NumberFieldPlace.comap (k := A.Fmod) v.1 =
      (withCanonicalPlaceSection R P hbad).V_mod_bijection.symm v :=
  (withCanonicalPlaceSection R P hbad).V_place_comap v

def toSourceSignQuotientData
    (R : SourceCompletionSignQuotient A) :
    SourceSignQuotientData A where
  xF := R.xF
  xF_geometry := R.xF_geometry
  ellipticInvolution := R.ellipticInvolution
  ellipticInvolution_squared := R.ellipticInvolution_squared
  unique_elliptic_involution := R.unique_elliptic_involution
  signAction := R.signAction
  signAction_inversion_eq_ellipticInvolution :=
    R.signAction_inversion_eq_ellipticInvolution
  cF := R.cF
  quotient := R.quotient
  quotientWitness := R.quotientWitness
  xFGroups := R.xFGroups
  cFGroups := R.cFGroups
  fGroupInclusion := R.fGroupInclusion
  xK := R.xK
  cK := R.cK
  xKExtension := R.xKExtension
  cKExtension := R.cKExtension
  xKType := R.xKType
  cKType := R.cKType
  xK_eq_extension := R.xK_eq_extension
  cK_eq_extension := R.cK_eq_extension
  V := R.V
  V_mod_bad := R.V_mod_bad
  V_mod_bad_odd_residue_characteristic :=
    R.V_mod_bad_odd_residue_characteristic
  V_mod_bad_nonempty := R.V_mod_bad_nonempty
  V_section := R.V_section
  V_eq_section := R.V_eq_section
  V_mod_bijection := R.V_mod_bijection
  V_place_comap := R.V_place_comap
  epsilon := R.epsilon

@[simp] theorem toSource_xF (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.xF = R.xF :=
  rfl

@[simp] theorem toSource_cF (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.cF = R.cF :=
  rfl

@[simp] theorem toSource_xK (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.xK = R.xK :=
  rfl

@[simp] theorem toSource_cK (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.cK = R.cK :=
  rfl

@[simp] theorem toSource_V (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.V = R.V :=
  rfl

@[simp] theorem toSource_V_mod_bad (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.V_mod_bad = R.V_mod_bad :=
  rfl

@[simp] theorem toSource_epsilon (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.epsilon = R.epsilon :=
  rfl

@[simp] theorem toSource_xF_geometry (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.xF_geometry = R.xF_geometry :=
  rfl

@[simp] theorem toSource_ellipticInvolution (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.ellipticInvolution = R.ellipticInvolution :=
  rfl

@[simp] theorem toSource_signAction (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.signAction = R.signAction :=
  rfl

@[simp] theorem toSource_quotient (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.quotient = R.quotient :=
  rfl

@[simp] theorem toSource_xFGroups (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.xFGroups = R.xFGroups :=
  rfl

@[simp] theorem toSource_cFGroups (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.cFGroups = R.cFGroups :=
  rfl

@[simp] theorem toSource_xKExtension (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.xKExtension = R.xKExtension :=
  rfl

@[simp] theorem toSource_cKExtension (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.cKExtension = R.cKExtension :=
  rfl

@[simp] theorem toSource_V_section (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.V_section = R.V_section :=
  rfl

@[simp] theorem toSource_V_mod_bijection (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.V_mod_bijection = R.V_mod_bijection :=
  rfl

@[simp] theorem toSource_V_place_comap (R : SourceCompletionSignQuotient A) :
    R.toSourceSignQuotientData.V_place_comap = R.V_place_comap :=
  rfl

/-! Conversely, a supplied source record can be repackaged without losing any
    of its fields. -/
def ofSourceSignQuotientData
    (S : SourceSignQuotientData A) : SourceCompletionSignQuotient A where
  xF := S.xF
  xF_geometry := S.xF_geometry
  ellipticInvolution := S.ellipticInvolution
  ellipticInvolution_squared := S.ellipticInvolution_squared
  unique_elliptic_involution := S.unique_elliptic_involution
  signAction := S.signAction
  signAction_inversion_eq_ellipticInvolution :=
    S.signAction_inversion_eq_ellipticInvolution
  cF := S.cF
  quotient := S.quotient
  quotientWitness := S.quotientWitness
  xFGroups := S.xFGroups
  cFGroups := S.cFGroups
  fGroupInclusion := S.fGroupInclusion
  xK := S.xK
  cK := S.cK
  xKExtension := S.xKExtension
  cKExtension := S.cKExtension
  xKType := S.xKType
  cKType := S.cKType
  xK_eq_extension := S.xK_eq_extension
  cK_eq_extension := S.cK_eq_extension
  V := S.V
  V_mod_bad := S.V_mod_bad
  V_mod_bad_odd_residue_characteristic :=
    S.V_mod_bad_odd_residue_characteristic
  V_mod_bad_nonempty := S.V_mod_bad_nonempty
  V_section := S.V_section
  V_eq_section := S.V_eq_section
  V_mod_bijection := S.V_mod_bijection
  V_place_comap := S.V_place_comap
  epsilon := S.epsilon

@[simp] theorem ofSource_toSource (S : SourceSignQuotientData A) :
    (ofSourceSignQuotientData S).toSourceSignQuotientData = S := by
  rfl

@[simp] theorem toSource_ofSource (R : SourceCompletionSignQuotient A) :
    ofSourceSignQuotientData R.toSourceSignQuotientData = R := by
  cases R
  rfl

end SourceCompletionSignQuotient

/-! The remaining fields are staged after the real sign quotient record has
    been constructed.  Clause records retain their exact dependent types. -/
structure SourceCompletion (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData.{u} l
  fbar : SourceFbarExtension.{u} arithmetic
  signQuotient : SourceCompletionSignQuotient arithmetic
  arithmeticPrelude : SourceArithmeticPrelude arithmetic
  arithmeticPrelude_placeSection :
    arithmeticPrelude.placeSection = signQuotient.V_section
  clauseA : SourceClauseA arithmetic signQuotient.toSourceSignQuotientData
  clauseB : SourceClauseB arithmetic signQuotient.toSourceSignQuotientData clauseA
  clauseC : SourceClauseC arithmetic signQuotient.toSourceSignQuotientData
    clauseA clauseB
  clauseD : SourceClauseD arithmetic signQuotient.toSourceSignQuotientData
    clauseA clauseB clauseC
  clauseE : SourceClauseE arithmetic signQuotient.toSourceSignQuotientData
    clauseA clauseB clauseC clauseD
  clauseF : SourceClauseF arithmetic signQuotient.toSourceSignQuotientData
    clauseA clauseB clauseC clauseD clauseE

namespace SourceCompletion

variable {l : PrimeGeFive}
variable (C : SourceCompletion.{u} l)

noncomputable def arithmetic_spec : InitialThetaArithmeticData.{u} l :=
  C.arithmetic

noncomputable def arithmetic_prelude_spec :
    SourceArithmeticPrelude C.arithmetic :=
  C.arithmeticPrelude

/-! The source-supplied displayed closure and the arithmetic prelude's
    canonical closure are linked by their actual algebra equivalences.  This
    prevents the two fields from being treated as unrelated same-named
    carriers while retaining the source's freedom to choose an isomorphic
    algebraic closure. -/
noncomputable def source_fbar_to_arithmetic_prelude_fbar :
    C.fbar.carrier ≃ₐ[C.arithmetic.F]
      C.arithmeticPrelude.fbar.carrier :=
  C.fbar.comparison.trans C.arithmeticPrelude.fbar.comparison.symm

theorem source_fbar_to_arithmetic_prelude_fbar_commutes
    (r : C.arithmetic.F) :
    C.source_fbar_to_arithmetic_prelude_fbar
        (algebraMap C.arithmetic.F C.fbar.carrier r) =
      algebraMap C.arithmetic.F C.arithmeticPrelude.fbar.carrier r :=
  C.source_fbar_to_arithmetic_prelude_fbar.commutes r

theorem source_fbar_to_arithmetic_prelude_fbar_bijective :
    Function.Bijective C.source_fbar_to_arithmetic_prelude_fbar :=
  C.source_fbar_to_arithmetic_prelude_fbar.bijective

noncomputable def arithmetic_prelude_fbar_comparison :
    C.arithmeticPrelude.fbar.carrier ≃ₐ[C.arithmetic.F]
      AlgebraicClosure C.arithmetic.F :=
  C.arithmeticPrelude.fbar.comparison

theorem arithmetic_prelude_place_section_comap_lift
    (v : NumberFieldPlace C.arithmetic.Fmod) :
    NumberFieldPlace.comap (k := C.arithmetic.Fmod)
      (C.arithmeticPrelude.placeSection.lift v) = v :=
  C.arithmeticPrelude.placeSection.comap_lift v

theorem arithmetic_prelude_torsion_transport_bijective :
    Function.Bijective C.arithmeticPrelude.torsionTransport :=
  C.arithmeticPrelude.torsionTransport.bijective

noncomputable def fbar_spec : SourceFbarExtension C.arithmetic :=
  C.fbar

noncomputable def source_sign_quotient_spec :
    SourceSignQuotientData C.arithmetic :=
  C.signQuotient.toSourceSignQuotientData

noncomputable def source_clauseA_spec :
    SourceClauseA C.arithmetic C.signQuotient.toSourceSignQuotientData :=
  C.clauseA

theorem source_clauseB_spec :
    SourceClauseB C.arithmetic C.signQuotient.toSourceSignQuotientData C.clauseA :=
  C.clauseB

noncomputable def source_clauseC_spec :
    SourceClauseC C.arithmetic C.signQuotient.toSourceSignQuotientData
      C.clauseA C.clauseB :=
  C.clauseC

noncomputable def source_clauseD_spec :
    SourceClauseD C.arithmetic C.signQuotient.toSourceSignQuotientData
      C.clauseA C.clauseB C.clauseC :=
  C.clauseD

noncomputable def source_clauseE_spec :
    SourceClauseE C.arithmetic C.signQuotient.toSourceSignQuotientData
      C.clauseA C.clauseB C.clauseC C.clauseD :=
  C.clauseE

noncomputable def source_clauseF_spec :
    SourceClauseF C.arithmetic C.signQuotient.toSourceSignQuotientData
      C.clauseA C.clauseB C.clauseC C.clauseD C.clauseE :=
  C.clauseF

/-! Stage projections retain the exact dependent types. -/
def sourceSignQuotientData : SourceSignQuotientData C.arithmetic :=
  C.signQuotient.toSourceSignQuotientData

/-! The displayed tuple is constructed from the same source record.  The
    equalities are reflexive because the displayed objects are not copied from
    another carrier. -/
def tuple : SourceInitialThetaTuple C.arithmetic where
  fbar := C.fbar
  source := C.sourceSignQuotientData
  xF := C.sourceSignQuotientData.xF
  xF_eq_source := rfl
  cK := C.sourceSignQuotientData.cK
  cK_eq_source := rfl
  V := C.sourceSignQuotientData.V
  V_eq_source := rfl
  V_mod_bad := C.sourceSignQuotientData.V_mod_bad
  V_mod_bad_eq_source := rfl
  epsilon := C.sourceSignQuotientData.epsilon
  epsilon_eq_source := rfl

@[simp] theorem tuple_source :
    (C.tuple).source = C.sourceSignQuotientData :=
  rfl

@[simp] theorem tuple_fbar : (C.tuple).fbar = C.fbar :=
  rfl

@[simp] theorem tuple_xF :
    (C.tuple).xF = C.sourceSignQuotientData.xF :=
  rfl

@[simp] theorem tuple_cK :
    (C.tuple).cK = C.sourceSignQuotientData.cK :=
  rfl

@[simp] theorem tuple_V :
    (C.tuple).V = C.sourceSignQuotientData.V :=
  rfl

@[simp] theorem tuple_V_mod_bad :
    (C.tuple).V_mod_bad = C.sourceSignQuotientData.V_mod_bad :=
  rfl

@[simp] theorem tuple_epsilon :
    (C.tuple).epsilon = C.sourceSignQuotientData.epsilon :=
  rfl

theorem tuple_fbar_comparison :
    (C.tuple).fbar.comparison = C.fbar.comparison :=
  rfl

theorem tuple_xF_source_eq : (C.tuple).xF = (C.tuple).source.xF :=
  rfl

theorem tuple_cK_source_eq : (C.tuple).cK = (C.tuple).source.cK :=
  rfl

theorem tuple_V_source_eq : (C.tuple).V = (C.tuple).source.V :=
  rfl

theorem tuple_V_mod_bad_source_eq :
    (C.tuple).V_mod_bad = (C.tuple).source.V_mod_bad :=
  rfl

theorem tuple_epsilon_source_eq :
    (C.tuple).epsilon = (C.tuple).source.epsilon :=
  rfl

def sourceClauseA :
    SourceClauseA C.arithmetic (C.sourceSignQuotientData) :=
  C.clauseA

theorem sourceClauseB :
    SourceClauseB C.arithmetic C.sourceSignQuotientData C.sourceClauseA :=
  C.clauseB

def sourceClauseC :
    SourceClauseC C.arithmetic C.sourceSignQuotientData C.sourceClauseA
      C.sourceClauseB :=
  C.clauseC

def sourceClauseD :
    SourceClauseD C.arithmetic C.sourceSignQuotientData C.sourceClauseA
      C.sourceClauseB C.sourceClauseC :=
  C.clauseD

def sourceClauseE :
    SourceClauseE C.arithmetic C.sourceSignQuotientData C.sourceClauseA
      C.sourceClauseB C.sourceClauseC C.sourceClauseD :=
  C.clauseE

def sourceClauseF :
    SourceClauseF C.arithmetic C.sourceSignQuotientData C.sourceClauseA
      C.sourceClauseB C.sourceClauseC C.sourceClauseD C.sourceClauseE :=
  C.clauseF

@[simp] theorem sourceSignQuotientData_eq :
    C.sourceSignQuotientData = C.signQuotient.toSourceSignQuotientData :=
  rfl

@[simp] theorem sourceClauseA_eq : C.sourceClauseA = C.clauseA :=
  rfl

@[simp] theorem sourceClauseB_eq : C.sourceClauseB = C.clauseB :=
  rfl

@[simp] theorem sourceClauseC_eq : C.sourceClauseC = C.clauseC :=
  rfl

@[simp] theorem sourceClauseD_eq : C.sourceClauseD = C.clauseD :=
  rfl

@[simp] theorem sourceClauseE_eq : C.sourceClauseE = C.clauseE :=
  rfl

@[simp] theorem sourceClauseF_eq : C.sourceClauseF = C.clauseF :=
  rfl

/-! The first assembly step creates the native dependent source datum. -/
def toSourceNativeInitialThetaData : SourceNativeInitialThetaData.{u} l where
  arithmetic := C.arithmetic
  tuple := C.tuple
  clauseA := C.sourceClauseA
  clauseB := C.sourceClauseB
  clauseC := C.sourceClauseC
  clauseD := C.sourceClauseD
  clauseE := C.sourceClauseE
  clauseF := C.sourceClauseF

theorem toSourceNative_arithmetic :
    C.toSourceNativeInitialThetaData.arithmetic = C.arithmetic :=
  rfl

theorem toSourceNative_tuple :
    C.toSourceNativeInitialThetaData.tuple = C.tuple :=
  rfl

theorem toSourceNative_source :
    C.toSourceNativeInitialThetaData.tuple.source = C.sourceSignQuotientData :=
  rfl

theorem toSourceNative_clauseA :
    C.toSourceNativeInitialThetaData.clauseA = C.clauseA :=
  rfl

theorem toSourceNative_clauseB :
    C.toSourceNativeInitialThetaData.clauseB = C.clauseB :=
  rfl

theorem toSourceNative_clauseC :
    C.toSourceNativeInitialThetaData.clauseC = C.clauseC :=
  rfl

theorem toSourceNative_clauseD :
    C.toSourceNativeInitialThetaData.clauseD = C.clauseD :=
  rfl

theorem toSourceNative_clauseE :
    C.toSourceNativeInitialThetaData.clauseE = C.clauseE :=
  rfl

theorem toSourceNative_clauseF :
    C.toSourceNativeInitialThetaData.clauseF = C.clauseF :=
  rfl

theorem toSourceNative_predicate :
    SourceNativeInitialThetaPredicate
      C.toSourceNativeInitialThetaData.arithmetic
      C.toSourceNativeInitialThetaData.tuple := by
  exact sourceNativeInitialThetaData_predicate C.toSourceNativeInitialThetaData

theorem toSourceNative_arithmetic_eq :
    C.toSourceNativeInitialThetaData.arithmetic = C.arithmetic :=
  C.toSourceNative_arithmetic

/-! The source completion does not silently change the arithmetic input. -/
theorem toSourceNative_recovery :
    C.toSourceNativeInitialThetaData.arithmetic = C.arithmetic :=
  C.toSourceNative_arithmetic

/-! ## Source-field evidence exposed by the completion

    These declarations are projections of the actual source records.  They
    are intentionally named by the source object they expose, so downstream
    constructions can consume a completion without reopening a dependent
    record or confusing a selected field with a newly constructed carrier. -/

theorem xF_geometry_spec :
    SourceOncePuncturedGeometry C.arithmetic.curve
      C.signQuotient.xF :=
  C.signQuotient.xF_geometry

noncomputable def elliptic_involution_squared_spec :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp
        C.signQuotient.ellipticInvolution C.signQuotient.ellipticInvolution)
      (Iut.HyperbolicOrbicurve.Hom.id C.signQuotient.xF) :=
  C.signQuotient.ellipticInvolution_squared

theorem unique_elliptic_involution_spec
    (inv : C.signQuotient.xF.Hom C.signQuotient.xF)
    (hinv : Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
      (Iut.HyperbolicOrbicurve.Hom.id C.signQuotient.xF)) :
    inv = C.signQuotient.ellipticInvolution :=
  C.signQuotient.unique_elliptic_involution inv hinv

noncomputable def sign_action_spec :
    Iut.OrbicurveSignAction C.signQuotient.xF :=
  C.signQuotient.signAction

theorem sign_action_inversion_spec :
    C.signQuotient.signAction.inversion =
      C.signQuotient.ellipticInvolution :=
  C.signQuotient.signAction_inversion_eq_ellipticInvolution

noncomputable def quotient_spec :
    Iut.OrbicurveSignInvariantMorphism C.signQuotient.signAction
      C.signQuotient.cF :=
  C.signQuotient.quotient

noncomputable def quotient_witness_spec :
    Iut.OrbicurveSignQuotientWitness C.signQuotient.signAction
      C.signQuotient.quotient :=
  C.signQuotient.quotientWitness

noncomputable def xF_groups_spec :
    SourceOrbicurveGroupData C.signQuotient.xF
      (Iut.AbsoluteGaloisProfinite C.arithmetic.F) :=
  C.signQuotient.xFGroups

noncomputable def cF_groups_spec :
    SourceOrbicurveGroupData C.signQuotient.cF
      (Iut.AbsoluteGaloisProfinite C.arithmetic.F) :=
  C.signQuotient.cFGroups

noncomputable def f_group_inclusion_spec :
    Iut.ProfiniteFundamentalGroupInclusion
      C.signQuotient.xFGroups.sequence.geometric
      C.signQuotient.xFGroups.sequence.arithmetic
      C.signQuotient.cFGroups.sequence.geometric
      C.signQuotient.cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite C.arithmetic.F)
      C.signQuotient.xFGroups.sequence C.signQuotient.cFGroups.sequence :=
  C.signQuotient.fGroupInclusion

noncomputable def xK_spec :
    Iut.HyperbolicOrbicurve C.arithmetic.K :=
  C.signQuotient.xK

noncomputable def cK_spec :
    Iut.HyperbolicOrbicurve C.arithmetic.K :=
  C.signQuotient.cK

noncomputable def xK_extension_spec :
    SourceOrbicurveScalarExtension C.arithmetic.F C.arithmetic.K
      C.signQuotient.xF :=
  C.signQuotient.xKExtension

noncomputable def cK_extension_spec :
    SourceOrbicurveScalarExtension C.arithmetic.F C.arithmetic.K
      C.signQuotient.cF :=
  C.signQuotient.cKExtension

theorem xK_type_spec :
    C.signQuotient.xK.signature = sourceTypeOneLTorsion l :=
  C.signQuotient.xKType

theorem cK_type_spec :
    C.signQuotient.cK.signature = sourceTypeOneLTorsionPlusMinus l :=
  C.signQuotient.cKType

theorem xK_extension_equality_spec :
    C.signQuotient.xK = C.signQuotient.xKExtension.result :=
  C.signQuotient.xK_eq_extension

theorem cK_extension_equality_spec :
    C.signQuotient.cK = C.signQuotient.cKExtension.result :=
  C.signQuotient.cK_eq_extension

theorem selected_places_spec :
    C.signQuotient.V = C.signQuotient.V_section.selected :=
  C.signQuotient.V_eq_section

noncomputable def selected_place_equivalence_spec :
    NumberFieldPlace C.arithmetic.Fmod ≃
      {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V} :=
  C.signQuotient.V_mod_bijection

theorem selected_place_comap_spec
    (v : {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V}) :
    NumberFieldPlace.comap (k := C.arithmetic.Fmod) v.1 =
      C.signQuotient.V_mod_bijection.symm v :=
  C.signQuotient.V_place_comap v

theorem bad_places_nonempty_spec : C.signQuotient.V_mod_bad.Nonempty :=
  C.signQuotient.V_mod_bad_nonempty

theorem bad_place_odd_residue_spec
    (p : NumberField.FinitePlace C.arithmetic.Fmod)
    (hp : p ∈ C.signQuotient.V_mod_bad) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  C.signQuotient.V_mod_bad_odd_residue_characteristic p hp

noncomputable def epsilon_spec :
    Iut.OrbicurveBoundaryCusp C.signQuotient.cK :=
  C.signQuotient.epsilon

theorem clauseA_stable_reduction_spec
    (p : NumberField.FinitePlace C.arithmetic.F) :
    C.arithmetic.curve.HasStableReductionAt p :=
  C.clauseA.stable_reduction_nonarchimedean p

noncomputable def clauseA_field_of_moduli_spec :
    SourceFieldOfModuli C.arithmetic :=
  C.clauseA.field_of_moduli

noncomputable def clauseA_maximal_extension_spec :
    IntermediateField C.arithmetic.Fmod C.arithmetic.F :=
  C.clauseA.maximal_solvable_extension

theorem clauseA_maximal_extension_property_spec :
    isFiniteSolvableGaloisSubextension
      C.clauseA.maximal_solvable_extension :=
  C.clauseA.maximal_solvable_property

theorem clauseA_maximal_extension_contains_spec
    (E : IntermediateField C.arithmetic.Fmod C.arithmetic.F)
    (hE : isFiniteSolvableGaloisSubextension E) :
    E ≤ C.clauseA.maximal_solvable_extension :=
  C.clauseA.maximal_solvable_contains E hE

theorem clauseB_multiplicative_spec
    (p : NumberField.FinitePlace C.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap (k := C.arithmetic.Fmod) p ∈
      C.signQuotient.V_mod_bad) :
    C.arithmetic.curve.HasMultiplicativeReductionAt p :=
  C.clauseB.multiplicative_over_bad p hp

theorem clauseB_q_comparison_spec
    (p : NumberField.FinitePlace C.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap (k := C.arithmetic.Fmod) p ∈
      C.signQuotient.V_mod_bad) :
    Nonempty (SourceTateComparisonWitness C.arithmetic p) :=
  C.clauseB.q_comparison p hp

theorem clauseB_residue_characteristic_coprime_spec
    (p : NumberField.FinitePlace C.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap (k := C.arithmetic.Fmod) p ∈
      C.signQuotient.V_mod_bad) :
    Nat.Coprime l.value
      (NumberFieldFinitePlace.residueCharacteristic
        (NumberFieldFinitePlace.comap (k := C.arithmetic.Fmod) p)) :=
  C.clauseB.residue_characteristic_prime_to_l p hp

theorem clauseC_torsion23_spec :
    PuncturedEllipticCurve.Torsion23Rational C.arithmetic.curve :=
  C.clauseC.torsion23_rational

noncomputable def clauseC_torsion_basis_spec :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      C.arithmetic.curve.LTorsion l :=
  C.clauseC.torsion_basis

noncomputable def clauseC_k_torsion_basis_spec :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      (C.arithmetic.curve.baseChange C.arithmetic.K).LTorsion l :=
  C.clauseC.k_torsion_basis

noncomputable def clauseC_k_to_f_torsion_transport_spec :
    (C.arithmetic.curve.baseChange C.arithmetic.K).LTorsion l ≃ₗ[ZMod l.value]
      C.arithmetic.curve.LTorsion l :=
  C.clauseC.k_to_f_torsion_transport

theorem clauseC_k_torsion_basis_transport_spec :
    C.clauseC.k_torsion_basis.trans C.clauseC.k_to_f_torsion_transport =
      C.clauseC.torsion_basis :=
  C.clauseC.k_torsion_basis_transport_eq_f_torsion_basis

noncomputable def clauseC_representation_spec :
    (SourceAbsoluteGalois C.arithmetic) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value) :=
  C.clauseC.representation

theorem clauseC_representation_canonical_spec :
    C.clauseC.representation =
      C.arithmetic.curve.galoisLTorsionMatrixRepresentation l
        C.clauseC.torsion_basis :=
  C.clauseC.representation_eq_canonical

theorem clauseC_image_contains_SL2_spec :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      C.clauseC.representation.range :=
  C.clauseC.image_contains_SL2

noncomputable def clauseC_kernel_field_identification_spec :
    C.arithmetic.K ≃ₐ[C.arithmetic.F]
      C.arithmetic.curve.galoisLTorsionKernelField l C.clauseC.torsion_basis :=
  C.clauseC.kernel_field_identification

theorem clauseC_kernel_field_range_spec :
    Set.range (fun x : C.arithmetic.K =>
      (C.clauseC.kernel_field_identification x : AlgebraicClosure C.arithmetic.F)) =
      (C.arithmetic.curve.galoisLTorsionKernelField l C.clauseC.torsion_basis :
        Set (AlgebraicClosure C.arithmetic.F)) :=
  C.clauseC.kernel_field_identification_range

noncomputable def clauseD_quotient_spec :
    Iut.OrbicurveSignInvariantMorphism C.clauseD.k_signAction
      C.signQuotient.cK :=
  C.clauseD.k_quotient

noncomputable def clauseD_quotient_witness_spec :
    Iut.OrbicurveSignQuotientWitness C.clauseD.k_signAction
      C.clauseD.k_quotient :=
  C.clauseD.k_quotientWitness

noncomputable def clauseD_torsion_cover_spec :
    SourceOrbicurveFiniteEtaleCover C.signQuotient.xK C.signQuotient.cK :=
  C.clauseD.k_l_torsion_cover

noncomputable def clauseD_x_groups_spec :
    SourceOrbicurveGroupData C.signQuotient.xK
      (Iut.AbsoluteGaloisProfinite C.arithmetic.K) :=
  C.clauseD.x_groups

noncomputable def clauseD_c_groups_spec :
    SourceOrbicurveGroupData C.signQuotient.cK
      (Iut.AbsoluteGaloisProfinite C.arithmetic.K) :=
  C.clauseD.c_groups

noncomputable def clauseD_group_inclusion_spec :
    Iut.ProfiniteFundamentalGroupInclusion
      C.clauseD.x_groups.sequence.geometric C.clauseD.x_groups.sequence.arithmetic
      C.clauseD.c_groups.sequence.geometric C.clauseD.c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite C.arithmetic.K)
      C.clauseD.x_groups.sequence C.clauseD.c_groups.sequence :=
  C.clauseD.group_inclusion

noncomputable def clauseD_x_to_F_embedding_spec :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      C.clauseD.x_groups.sequence.geometric C.clauseD.x_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite C.arithmetic.K)
      C.signQuotient.xFGroups.sequence.geometric
      C.signQuotient.xFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite C.arithmetic.F)
      C.clauseD.x_groups.sequence C.signQuotient.xFGroups.sequence :=
  C.clauseD.x_to_F_groups

noncomputable def clauseD_c_to_F_embedding_spec :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      C.clauseD.c_groups.sequence.geometric C.clauseD.c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite C.arithmetic.K)
      C.signQuotient.cFGroups.sequence.geometric
      C.signQuotient.cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite C.arithmetic.F)
      C.clauseD.c_groups.sequence C.signQuotient.cFGroups.sequence :=
  C.clauseD.c_to_F_groups

theorem clauseE_selected_eq_section_spec :
    C.signQuotient.V = C.signQuotient.V_section.selected :=
  C.clauseE.selected_eq_V

noncomputable def clauseE_selected_equiv_spec :
    NumberFieldPlace C.arithmetic.Fmod ≃
      {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V} :=
  C.clauseE.selected_equiv

noncomputable def clauseE_finite_local_spec
    (v : {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V})
    (hv : v.1.IsFinite) :
    SourceFiniteLocalSource C.arithmetic C.sourceSignQuotientData
      C.sourceClauseA C.sourceClauseB C.sourceClauseC C.sourceClauseD
      (selectedFinitePlace hv) :=
  C.clauseE.finite_local v hv

noncomputable def clauseE_infinite_local_spec
    (v : {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V})
    (hv : v.1.IsInfinite) :
    SourceInfiniteLocalSource C.arithmetic C.sourceSignQuotientData
      C.sourceClauseA C.sourceClauseB C.sourceClauseC C.sourceClauseD
      (selectedInfinitePlace hv) :=
  C.clauseE.infinite_local v hv

theorem clauseE_finite_local_curve_spec
    (v : {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V})
    (hv : v.1.IsFinite) :
    (C.clauseE.finite_local v hv).localCurve =
      sourceFiniteLocalCurve C.arithmetic (selectedFinitePlace hv) :=
  (C.clauseE.finite_local v hv).local_curve_eq_actual

theorem clauseE_infinite_local_curve_spec
    (v : {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V})
    (hv : v.1.IsInfinite) :
    (C.clauseE.infinite_local v hv).localCurve =
      sourceInfiniteLocalCurve C.arithmetic (selectedInfinitePlace hv) :=
  (C.clauseE.infinite_local v hv).local_curve_eq_actual

noncomputable def clauseE_finite_local_x_groups_spec
    (v : {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V})
    (hv : v.1.IsFinite) :
    SourceOrbicurveGroupData
      (C.clauseE.finite_local v hv).xExtension.result
      (Iut.AbsoluteGaloisProfinite
        (NumberFieldFinitePlace.Completion (selectedFinitePlace hv))) :=
  (C.clauseE.finite_local v hv).xGroups

noncomputable def clauseE_finite_local_c_groups_spec
    (v : {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V})
    (hv : v.1.IsFinite) :
    SourceOrbicurveGroupData
      (C.clauseE.finite_local v hv).cExtension.result
      (Iut.AbsoluteGaloisProfinite
        (NumberFieldFinitePlace.Completion (selectedFinitePlace hv))) :=
  (C.clauseE.finite_local v hv).cGroups

noncomputable def clauseE_infinite_local_x_groups_spec
    (v : {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V})
    (hv : v.1.IsInfinite) :
    SourceOrbicurveGroupData
      (C.clauseE.infinite_local v hv).xExtension.result
      (Iut.AbsoluteGaloisProfinite
        (selectedInfinitePlace hv).Completion) :=
  (C.clauseE.infinite_local v hv).xGroups

noncomputable def clauseE_infinite_local_c_groups_spec
    (v : {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V})
    (hv : v.1.IsInfinite) :
    SourceOrbicurveGroupData
      (C.clauseE.infinite_local v hv).cExtension.result
      (Iut.AbsoluteGaloisProfinite
        (selectedInfinitePlace hv).Completion) :=
  (C.clauseE.infinite_local v hv).cGroups

noncomputable def clauseE_finite_local_x_global_embedding_spec
    (v : {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V})
    (hv : v.1.IsFinite) :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      (C.clauseE.finite_local v hv).xGroups.sequence.geometric
      (C.clauseE.finite_local v hv).xGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite
        (NumberFieldFinitePlace.Completion (selectedFinitePlace hv)))
      C.clauseD.x_groups.sequence.geometric C.clauseD.x_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite C.arithmetic.K)
      (C.clauseE.finite_local v hv).xGroups.sequence C.clauseD.x_groups.sequence :=
  (C.clauseE.finite_local v hv).xGlobalEmbedding

noncomputable def clauseE_finite_local_c_global_embedding_spec
    (v : {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V})
    (hv : v.1.IsFinite) :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      (C.clauseE.finite_local v hv).cGroups.sequence.geometric
      (C.clauseE.finite_local v hv).cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite
        (NumberFieldFinitePlace.Completion (selectedFinitePlace hv)))
      C.clauseD.c_groups.sequence.geometric C.clauseD.c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite C.arithmetic.K)
      (C.clauseE.finite_local v hv).cGroups.sequence C.clauseD.c_groups.sequence :=
  (C.clauseE.finite_local v hv).cGlobalEmbedding

noncomputable def clauseE_infinite_local_x_global_embedding_spec
    (v : {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V})
    (hv : v.1.IsInfinite) :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      (C.clauseE.infinite_local v hv).xGroups.sequence.geometric
      (C.clauseE.infinite_local v hv).xGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite
        (selectedInfinitePlace hv).Completion)
      C.clauseD.x_groups.sequence.geometric C.clauseD.x_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite C.arithmetic.K)
      (C.clauseE.infinite_local v hv).xGroups.sequence C.clauseD.x_groups.sequence :=
  (C.clauseE.infinite_local v hv).xGlobalEmbedding

noncomputable def clauseE_infinite_local_c_global_embedding_spec
    (v : {v : NumberFieldPlace C.arithmetic.K // v ∈ C.signQuotient.V})
    (hv : v.1.IsInfinite) :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      (C.clauseE.infinite_local v hv).cGroups.sequence.geometric
      (C.clauseE.infinite_local v hv).cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite
        (selectedInfinitePlace hv).Completion)
      C.clauseD.c_groups.sequence.geometric C.clauseD.c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite C.arithmetic.K)
      (C.clauseE.infinite_local v hv).cGroups.sequence C.clauseD.c_groups.sequence :=
  (C.clauseE.infinite_local v hv).cGlobalEmbedding

noncomputable def clauseF_boundary_origin_spec :
    TorsionQuotientBoundaryOrigin l C.arithmetic C.signQuotient.cK :=
  C.clauseF.boundary_origin

theorem clauseF_quotient_basis_eq_k_torsion_basis_spec :
    C.clauseF.boundary_origin.rank_one_quotient.torsion_basis =
      C.clauseC.k_torsion_basis :=
  C.clauseF.quotient_basis_eq_k_torsion_basis

theorem clauseF_quotient_basis_transport_spec :
    C.clauseF.boundary_origin.rank_one_quotient.torsion_basis.trans
        C.clauseC.k_to_f_torsion_transport = C.clauseC.torsion_basis :=
  C.clauseF.quotient_basis_transport_spec

theorem clauseF_boundary_cusp_eq_epsilon_spec :
    C.clauseF.boundary_origin.cusp = C.signQuotient.epsilon :=
  C.clauseF.boundary_cusp_eq_epsilon

noncomputable def clauseF_cusp_decomposition_spec :
    Iut.OrbicurveCuspidalDecompositionData C.clauseD.c_groups.groups :=
  C.clauseF.cusp_decomposition

theorem clauseF_cusp_decomposition_origin_spec :
    C.clauseF.cusp_decomposition.cusp = C.clauseF.boundary_origin.cusp :=
  C.clauseF.cusp_decomposition_cusp_eq_origin

theorem clauseF_cusp_epsilon_spec :
    C.clauseF.cusp_decomposition.cusp = C.signQuotient.epsilon := by
  calc
    C.clauseF.cusp_decomposition.cusp = C.clauseF.boundary_origin.cusp :=
      C.clauseF.cusp_decomposition_cusp_eq_origin
    _ = C.signQuotient.epsilon := C.clauseF.boundary_cusp_eq_epsilon

/-! Packaging an already supplied native source datum is the converse
    direction.  It is useful for transport and does not construct a native
    datum from arithmetic data. -/
def ofSourceNative (T : SourceNativeInitialThetaData.{u} l) : SourceCompletion.{u} l where
  arithmetic := T.arithmetic
  fbar := T.tuple.fbar
  signQuotient := SourceCompletionSignQuotient.ofSourceSignQuotientData
    T.tuple.source
  arithmeticPrelude := SourceArithmeticPrelude.fromPlaceSection
    T.arithmetic T.tuple.source.V_section
  arithmeticPrelude_placeSection := rfl
  clauseA := T.clauseA
  clauseB := T.clauseB
  clauseC := T.clauseC
  clauseD := T.clauseD
  clauseE := T.clauseE
  clauseF := T.clauseF

@[simp] theorem ofSourceNative_arithmetic
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).arithmetic = T.arithmetic :=
  rfl

@[simp] theorem ofSourceNative_fbar
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).fbar = T.tuple.fbar :=
  rfl

@[simp] theorem ofSourceNative_arithmeticPrelude
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).arithmeticPrelude =
      SourceArithmeticPrelude.fromPlaceSection
        T.arithmetic T.tuple.source.V_section :=
  rfl

theorem arithmeticPrelude_placeSection_spec
    (C : SourceCompletion.{u} l) :
    C.arithmeticPrelude.placeSection = C.signQuotient.V_section :=
  C.arithmeticPrelude_placeSection

noncomputable def arithmeticPrelude_selected_equiv
    (C : SourceCompletion.{u} l) :
    NumberFieldPlace C.arithmetic.Fmod ≃
      {v : NumberFieldPlace C.arithmetic.K //
        v ∈ C.arithmeticPrelude.selectedPlaces} :=
  C.arithmeticPrelude.selectedEquiv

theorem arithmeticPrelude_selected_place_comap
    (C : SourceCompletion.{u} l)
    (v : {v : NumberFieldPlace C.arithmetic.K //
      v ∈ C.arithmeticPrelude.selectedPlaces}) :
    NumberFieldPlace.comap (k := C.arithmetic.Fmod) v.1 =
      C.arithmeticPrelude.selectedEquiv.symm v :=
  C.arithmeticPrelude.selected_place_comap v

theorem arithmeticPrelude_selected_place_partition
    (C : SourceCompletion.{u} l) :
    C.arithmeticPrelude.selectedNonarchimedean ∪
        C.arithmeticPrelude.selectedArchimedean = Set.univ :=
  C.arithmeticPrelude.selected_nonarchimedean_or_archimedean_cover

theorem arithmeticPrelude_selected_place_partition_disjoint
    (C : SourceCompletion.{u} l) :
    Disjoint C.arithmeticPrelude.selectedNonarchimedean
      C.arithmeticPrelude.selectedArchimedean :=
  C.arithmeticPrelude.selected_nonarchimedean_archimedean_disjoint

theorem arithmeticPrelude_fbar_is_algClosed
    (C : SourceCompletion.{u} l) :
    IsAlgClosed C.arithmeticPrelude.fbar.carrier :=
  C.arithmeticPrelude.fbar_is_algebraically_closed

theorem arithmeticPrelude_fbar_is_algebraic
    (C : SourceCompletion.{u} l)
    (x : C.arithmeticPrelude.fbar.carrier) :
    IsAlgebraic C.arithmetic.F x :=
  C.arithmeticPrelude.fbar_is_algebraic x

theorem arithmeticPrelude_fbar_comparison_injective
    (C : SourceCompletion.{u} l) :
    Function.Injective C.arithmeticPrelude.fbar.comparison :=
  C.arithmeticPrelude.fbar_comparison_injective

theorem arithmeticPrelude_fbar_comparison_surjective
    (C : SourceCompletion.{u} l) :
    Function.Surjective C.arithmeticPrelude.fbar.comparison :=
  C.arithmeticPrelude.fbar_comparison_surjective

theorem arithmeticPrelude_torsionTransport_left_inverse
    (C : SourceCompletion.{u} l) :
    Function.LeftInverse C.arithmeticPrelude.torsionTransport.symm
      C.arithmeticPrelude.torsionTransport :=
  C.arithmeticPrelude.torsionTransport_left_inverse

theorem arithmeticPrelude_torsionTransport_right_inverse
    (C : SourceCompletion.{u} l) :
    Function.RightInverse C.arithmeticPrelude.torsionTransport.symm
      C.arithmeticPrelude.torsionTransport :=
  C.arithmeticPrelude.torsionTransport_right_inverse

theorem arithmeticPrelude_selected_finite_lift
    (C : SourceCompletion.{u} l)
    (p : NumberField.FinitePlace C.arithmetic.Fmod) :
    C.arithmeticPrelude.selectedEquiv (NumberFieldPlace.finite p) ∈
      C.arithmeticPrelude.selectedNonarchimedean :=
  C.arithmeticPrelude.selected_finite_lift_is_finite p

theorem arithmeticPrelude_selected_infinite_lift
    (C : SourceCompletion.{u} l)
    (v : NumberField.InfinitePlace C.arithmetic.Fmod) :
    C.arithmeticPrelude.selectedEquiv (NumberFieldPlace.infinite v) ∈
      C.arithmeticPrelude.selectedArchimedean :=
  C.arithmeticPrelude.selected_infinite_lift_is_archimedean v

theorem signQuotient_selectedPlaces_eq_prelude
    (C : SourceCompletion.{u} l) :
    C.signQuotient.V = C.arithmeticPrelude.selectedPlaces := by
  calc
    C.signQuotient.V = C.signQuotient.V_section.selected :=
      C.signQuotient.V_eq_section
    _ = C.arithmeticPrelude.placeSection.selected := by
      rw [← C.arithmeticPrelude_placeSection]
    _ = C.arithmeticPrelude.selectedPlaces := rfl

noncomputable def sourceCompletion_has_selected_equiv
    (C : SourceCompletion.{u} l) :
    NumberFieldPlace C.arithmetic.Fmod ≃
      {v : NumberFieldPlace C.arithmetic.K //
        v ∈ C.signQuotient.V} := by
  let e := C.arithmeticPrelude.selectedEquiv
  have hset : C.arithmeticPrelude.selectedPlaces = C.signQuotient.V := by
    exact (C.signQuotient_selectedPlaces_eq_prelude).symm
  exact e.trans (Equiv.setCongr hset)

theorem sourceCompletion_selected_place_comap
    (C : SourceCompletion.{u} l)
    (v : {v : NumberFieldPlace C.arithmetic.K //
      v ∈ C.signQuotient.V}) :
    NumberFieldPlace.comap (k := C.arithmetic.Fmod) v.1 =
      (C.sourceCompletion_has_selected_equiv).symm v := by
  have hset : C.arithmeticPrelude.selectedPlaces = C.signQuotient.V := by
    exact (C.signQuotient_selectedPlaces_eq_prelude).symm
  change NumberFieldPlace.comap (k := C.arithmetic.Fmod) v.1 = _
  have hv : v.1 ∈ C.arithmeticPrelude.selectedPlaces := by
    rw [hset]
    exact v.2
  simpa [sourceCompletion_has_selected_equiv, hset] using
    C.arithmeticPrelude.selected_place_comap
      (show {v : NumberFieldPlace C.arithmetic.K //
        v ∈ C.arithmeticPrelude.selectedPlaces} from ⟨v.1, hv⟩)

@[simp] theorem ofSourceNative_signQuotient
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).signQuotient =
      SourceCompletionSignQuotient.ofSourceSignQuotientData T.tuple.source :=
  rfl

@[simp] theorem ofSourceNative_clauseA
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).clauseA = T.clauseA :=
  rfl

@[simp] theorem ofSourceNative_clauseB
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).clauseB = T.clauseB :=
  rfl

@[simp] theorem ofSourceNative_clauseC
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).clauseC = T.clauseC :=
  rfl

@[simp] theorem ofSourceNative_clauseD
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).clauseD = T.clauseD :=
  rfl

@[simp] theorem ofSourceNative_clauseE
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).clauseE = T.clauseE :=
  rfl

@[simp] theorem ofSourceNative_clauseF
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).clauseF = T.clauseF :=
  rfl

theorem ofSourceNative_toSourceNative_arithmetic
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).toSourceNativeInitialThetaData.arithmetic = T.arithmetic :=
  rfl

theorem ofSourceNative_toSourceNative_source
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).toSourceNativeInitialThetaData.tuple.source =
      T.tuple.source :=
  rfl

theorem ofSourceNative_toSourceNative_clauseA
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).toSourceNativeInitialThetaData.clauseA = T.clauseA :=
  rfl

theorem ofSourceNative_toSourceNative_clauseB
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).toSourceNativeInitialThetaData.clauseB = T.clauseB :=
  rfl

theorem ofSourceNative_toSourceNative_clauseC
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).toSourceNativeInitialThetaData.clauseC = T.clauseC :=
  rfl

theorem ofSourceNative_toSourceNative_clauseD
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).toSourceNativeInitialThetaData.clauseD = T.clauseD :=
  rfl

theorem ofSourceNative_toSourceNative_clauseE
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).toSourceNativeInitialThetaData.clauseE = T.clauseE :=
  rfl

theorem ofSourceNative_toSourceNative_clauseF
    (T : SourceNativeInitialThetaData.{u} l) :
    (ofSourceNative T).toSourceNativeInitialThetaData.clauseF = T.clauseF :=
  rfl

/-! The source completion is inhabited exactly when a complete native source
    datum is supplied.  This equivalence is a packaging theorem, not the
    arithmetic-to-source existence theorem. -/
theorem nonempty_iff_native_nonempty (l : PrimeGeFive) :
    Nonempty (SourceCompletion.{u} l) ↔
      Nonempty (SourceNativeInitialThetaData.{u} l) := by
  constructor
  · intro h
    exact ⟨h.some.toSourceNativeInitialThetaData⟩
  · intro h
    exact ⟨ofSourceNative h.some⟩

theorem exists_iff_native_exists (l : PrimeGeFive) :
    (∃ _C : SourceCompletion.{u} l, True) ↔
      ∃ _T : SourceNativeInitialThetaData.{u} l, True := by
  constructor
  · rintro ⟨C, _⟩
    exact ⟨C.toSourceNativeInitialThetaData, trivial⟩
  · rintro ⟨T, _⟩
    exact ⟨ofSourceNative T, trivial⟩

end SourceCompletion

/-! The universal arithmetic gate is intentionally not defined here.  The
    only construction exposed by this module consumes an already supplied
    `SourceCompletion`, so all source conditions remain visible in its input. -/
theorem sourceCompletion_to_sourceNative
    {l : PrimeGeFive} (C : SourceCompletion.{u} l) :
    ∃ T : SourceNativeInitialThetaData.{u} l,
      T.arithmetic = C.arithmetic := by
  exact ⟨C.toSourceNativeInitialThetaData, C.toSourceNative_arithmetic⟩

end InitialThetaSource

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def initialThetaSourceCompletion : Obligation :=
  { id := "IUT-I.definition-3.1-source-completion-package"
    source := "IUT I, Definition 3.1(a)-(f), pp. 61-64"
    status := VerificationStatus.interface
    note :=
      "SourceCompletion explicitly carries the canonical algebraic-closure " ++
        "extension, actual SourceSignQuotientData, K-side torsion boundary " ++
        "carrier/transport fields, and dependent Clause A-F records. Its " ++
        "assembly into SourceNativeInitialThetaData is proved as " ++
        "a source-witness implication; no universal constructor from an " ++
        "arithmetic-only record is claimed."
    dependsOn := [ "IUT-I.definition-3.1-A2-quantifier-boundary" ] }

end LeanFormal.IUT.Audit
