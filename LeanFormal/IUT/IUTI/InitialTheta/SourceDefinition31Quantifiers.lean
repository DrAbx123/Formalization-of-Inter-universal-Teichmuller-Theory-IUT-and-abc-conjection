/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.Foundations.NumberField.Places
import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.Geometry.TatePointQuotientBoundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionTransport
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceSelection
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionRankOneQuotient
import Iut.Foundations.Orbicurve
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
  The public orbicurve foundation deliberately stops at the represented
  finite-etale category and the profinite exact-sequence primitives.  The
  printed Definition 3.1 uses the corresponding aggregate records, so this
  file introduces those records from the public primitives.  No carrier is
  added here: the arithmetic group is the certified group of the actual
  finite-etale category, and the geometric group is the closed kernel of its
  actual projection.
-/

namespace Iut

universe u

noncomputable section

structure OrbicurveFundamentalGroupData
    {F : Type u} [Field F]
    (X : HyperbolicOrbicurve F)
    (galois : ProfiniteGrp.{u}) where
  arithmeticGroup : ProfiniteGrp.{u}
  arithmetic : OrbicurveEtaleFundamentalGroup X arithmeticGroup
  projection : arithmeticGroup ⟶ galois
  projection_surjective : Function.Surjective projection
  geometric :
    OrbicurveEtaleFundamentalGroup X
      (closedSubgroupProfiniteGrp
        (profiniteKernelClosedSubgroup projection))

namespace OrbicurveFundamentalGroupData

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}
variable {galois : ProfiniteGrp.{u}}

noncomputable def exactSequence
    (groups : OrbicurveFundamentalGroupData X galois) :
    ProfiniteFundamentalExactSequence
      groups.geometric.group groups.arithmetic.group galois :=
  profiniteKernelExactSequence groups.projection groups.projection_surjective

end OrbicurveFundamentalGroupData

structure OrbicurveCuspidalDecompositionData
    {F : Type u} [Field F]
    {X : HyperbolicOrbicurve F}
    {galois : ProfiniteGrp.{u}}
    (groups : OrbicurveFundamentalGroupData X galois) where
  cusp : OrbicurveBoundaryCusp X
  decompositionSubgroup : ClosedSubgroup groups.arithmetic.group
  decompositionProjection_surjective :
    Function.Surjective
      (profiniteClosedSubgroupRestriction
        decompositionSubgroup groups.projection)

namespace OrbicurveCuspidalDecompositionData

variable {F : Type u} [Field F]
variable {X : HyperbolicOrbicurve F}
variable {galois : ProfiniteGrp.{u}}
variable {groups : OrbicurveFundamentalGroupData X galois}

noncomputable def decomposition
    (data : OrbicurveCuspidalDecompositionData groups) :
    ProfiniteGrp.{u} :=
  closedSubgroupProfiniteGrp data.decompositionSubgroup

noncomputable def decompositionProjection
    (data : OrbicurveCuspidalDecompositionData groups) :
    data.decomposition ⟶ galois :=
  profiniteClosedSubgroupRestriction
    data.decompositionSubgroup groups.projection

noncomputable def inertia
    (data : OrbicurveCuspidalDecompositionData groups) :
    ProfiniteGrp.{u} :=
  closedSubgroupProfiniteGrp
    (profiniteKernelClosedSubgroup data.decompositionProjection)

noncomputable def exactSequence
    (data : OrbicurveCuspidalDecompositionData groups) :
    ProfiniteFundamentalExactSequence
      data.inertia data.decomposition galois :=
  profiniteKernelExactSequence
    data.decompositionProjection
    data.decompositionProjection_surjective

noncomputable def ambientEmbedding
    (data : OrbicurveCuspidalDecompositionData groups) :
    ProfiniteFundamentalExactSequenceEmbedding
      data.inertia data.decomposition galois
      groups.geometric.group groups.arithmetic.group galois
      data.exactSequence groups.exactSequence :=
  profiniteClosedSubgroupExactSequenceEmbedding
    data.decompositionSubgroup groups.projection
    groups.projection_surjective
    data.decompositionProjection_surjective

end OrbicurveCuspidalDecompositionData

end

end Iut

/-! The exact-sequence carriers are parameters of the structure, not fields.
    These projections expose those certified parameters for the source
    records' diagram declarations. -/
namespace Iut.ProfiniteFundamentalExactSequence

universe u

abbrev geometric
    {Ggeom Garith Galois : ProfiniteGrp.{u}}
    (_sequence : ProfiniteFundamentalExactSequence Ggeom Garith Galois) :
    ProfiniteGrp.{u} :=
  Ggeom

abbrev arithmetic
    {Ggeom Garith Galois : ProfiniteGrp.{u}}
    (_sequence : ProfiniteFundamentalExactSequence Ggeom Garith Galois) :
    ProfiniteGrp.{u} :=
  Garith

end Iut.ProfiniteFundamentalExactSequence

/-!
  # IUT I, Definition 3.1: the initial Theta-data quantifier

  The paper quantifies over a supplied collection
  `(Fbar/F, X_{F,l}, C_K, V, V_mod^bad, epsilon)` and then imposes clauses
  (a)--(f).  This file is the source boundary for that statement.  Every
  carrier in the boundary is an actual field, curve, place, stack, profinite
  group, or Tate comparison from the foundations.  In particular, this file
  does not import the older `SourceInitialThetaData`, whose carrier fields were
  intentionally weaker than the printed definition.

  A source datum is an input satisfying the printed hypotheses.  The structure
  does not claim that an arbitrary arithmetic record has such an inhabitant;
  the existence theorem would be a separate mathematical result.
-/

namespace LeanFormal.IUT

open scoped MatrixGroups

noncomputable section

universe u

namespace InitialThetaSource

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open Iut
open scoped Pseudofunctor.StrongTrans
open scoped SpecOfNotation

/-! ## Actual tuple objects -/

abbrev SourceFbar (A : InitialThetaArithmeticData l) : Type u :=
  AlgebraicClosure A.F

abbrev SourceAbsoluteGalois (A : InitialThetaArithmeticData l) :=
  SourceFbar A ≃ₐ[A.F] SourceFbar A

/-! The first entry of Definition 3.1 is the algebraic-closure extension
    `Fbar/F`, not an element of the algebraic closure.  This record keeps the
    extension carrier and all of its field-theoretic certificates together.
    The comparison is an actual algebra equivalence, so an isomorphic chosen
    algebraic closure may be transported without weakening the source datum. -/
structure SourceFbarExtension
    (A : InitialThetaArithmeticData l) where
  carrier : Type u
  [fieldCarrier : Field carrier]
  [algebraCarrier : Algebra A.F carrier]
  [algebraicCarrier : Algebra.IsAlgebraic A.F carrier]
  [closedCarrier : IsAlgClosed carrier]
  comparison : carrier ≃ₐ[A.F] AlgebraicClosure A.F

attribute [instance] SourceFbarExtension.fieldCarrier
  SourceFbarExtension.algebraCarrier
  SourceFbarExtension.algebraicCarrier
  SourceFbarExtension.closedCarrier

namespace SourceFbarExtension

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData l}

noncomputable def comparison_is_algebraEquiv
    (E : SourceFbarExtension A) :
    E.carrier ≃ₐ[A.F] AlgebraicClosure A.F :=
  E.comparison

theorem carrier_is_algClosed
    (E : SourceFbarExtension A) : IsAlgClosed E.carrier :=
  inferInstance

theorem carrier_is_algebraic
    (E : SourceFbarExtension A) (x : E.carrier) :
    IsAlgebraic A.F x :=
  Algebra.IsAlgebraic.isAlgebraic x

theorem comparison_injective
    (E : SourceFbarExtension A) : Function.Injective E.comparison :=
  E.comparison.injective

theorem comparison_surjective
    (E : SourceFbarExtension A) : Function.Surjective E.comparison :=
  E.comparison.surjective

theorem comparison_map_zero
    (E : SourceFbarExtension A) : E.comparison 0 = 0 :=
  map_zero E.comparison

theorem comparison_map_one
    (E : SourceFbarExtension A) : E.comparison 1 = 1 :=
  map_one E.comparison

theorem comparison_map_add
    (E : SourceFbarExtension A) (x y : E.carrier) :
    E.comparison (x + y) = E.comparison x + E.comparison y :=
  map_add E.comparison x y

theorem comparison_map_mul
    (E : SourceFbarExtension A) (x y : E.carrier) :
    E.comparison (x * y) = E.comparison x * E.comparison y :=
  map_mul E.comparison x y

theorem comparison_map_smul
    (E : SourceFbarExtension A) (r : A.F) (x : E.carrier) :
    E.comparison (r • x) = r • E.comparison x :=
by
  simp only [Algebra.smul_def, map_mul, E.comparison.commutes]

/-! The canonical extension is the actual Mathlib algebraic closure.  It is
    the only construction in this file that needs no source hypothesis. -/
noncomputable def canonical (A : InitialThetaArithmeticData l) :
    SourceFbarExtension A where
  carrier := AlgebraicClosure A.F
  comparison := (AlgEquiv.refl :
    AlgebraicClosure A.F ≃ₐ[A.F] AlgebraicClosure A.F)

@[simp] theorem canonical_carrier
    (A : InitialThetaArithmeticData l) :
    (canonical A).carrier = AlgebraicClosure A.F :=
  rfl

@[simp] theorem canonical_comparison
    (A : InitialThetaArithmeticData l) :
    (canonical A).comparison = (AlgEquiv.refl :
      AlgebraicClosure A.F ≃ₐ[A.F] AlgebraicClosure A.F) :=
  rfl

theorem canonical_is_algClosed
    (A : InitialThetaArithmeticData l) :
    IsAlgClosed (canonical A).carrier :=
  inferInstance

theorem canonical_is_algebraic
    (A : InitialThetaArithmeticData l) (x : (canonical A).carrier) :
    IsAlgebraic A.F x :=
  Algebra.IsAlgebraic.isAlgebraic x

theorem comparison_respects_base
    (E : SourceFbarExtension A) (r : A.F) :
    E.comparison (algebraMap A.F E.carrier r) =
      algebraMap A.F (AlgebraicClosure A.F) r := by
  exact E.comparison.commutes r

end SourceFbarExtension

def sourceTypeOneOne : Iut.OrbicurveSignature where
  genus := 1
  stackyOrders := []
  punctures := 1
  stackyOrders_ge_two := by simp

def sourceTypeOneOnePlusMinus : Iut.OrbicurveSignature where
  genus := 1
  stackyOrders := [2]
  punctures := 0
  stackyOrders_ge_two := by
    intro m hm
    simp only [List.mem_singleton] at hm
    rcases hm with rfl
    decide

def sourceTypeOneLTorsion (l : PrimeGeFive) : Iut.OrbicurveSignature where
  genus := 1
  stackyOrders := [l.value]
  punctures := 0
  stackyOrders_ge_two := by
    intro m hm
    simp only [List.mem_singleton] at hm
    subst m
    exact l.ge_five.trans' (by decide)

def sourceTypeOneLTorsionPlusMinus (l : PrimeGeFive) : Iut.OrbicurveSignature where
  genus := 1
  stackyOrders := [2, l.value]
  punctures := 0
  stackyOrders_ge_two := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · decide
    · have hfive := l.ge_five
      omega

theorem sourceTypeOneOne_hyperbolic : sourceTypeOneOne.IsHyperbolic := by
  norm_num [sourceTypeOneOne, Iut.OrbicurveSignature.IsHyperbolic,
    Iut.OrbicurveSignature.eulerCharacteristic]

theorem sourceTypeOneOnePlusMinus_hyperbolic :
    sourceTypeOneOnePlusMinus.IsHyperbolic := by
  norm_num [sourceTypeOneOnePlusMinus, Iut.OrbicurveSignature.IsHyperbolic,
    Iut.OrbicurveSignature.eulerCharacteristic]

theorem sourceTypeOneLTorsion_hyperbolic (l : PrimeGeFive) :
    (sourceTypeOneLTorsion l).IsHyperbolic := by
  have hfive := l.ge_five
  have htwoNat : 2 < l.value := by omega
  have hpos : (0 : ℚ) < l.value := by
    exact_mod_cast l.prime.pos
  have htwo : (2 : ℚ) < (l.value : ℚ) := by
    exact_mod_cast htwoNat
  have hinv_two : (l.value : ℚ)⁻¹ < (2 : ℚ)⁻¹ := by
    exact (inv_lt_inv₀ hpos (by norm_num : (0 : ℚ) < 2)).2 htwo
  have hinv : (l.value : ℚ)⁻¹ < 1 :=
    hinv_two.trans (two_inv_lt_one (α := ℚ))
  norm_num [sourceTypeOneLTorsion, Iut.OrbicurveSignature.IsHyperbolic,
    Iut.OrbicurveSignature.eulerCharacteristic]
  exact hinv

theorem sourceTypeOneLTorsionPlusMinus_hyperbolic (l : PrimeGeFive) :
    (sourceTypeOneLTorsionPlusMinus l).IsHyperbolic := by
  have hfive := l.ge_five
  have htwoNat : 2 < l.value := by omega
  have hpos : (0 : ℚ) < l.value := by
    exact_mod_cast l.prime.pos
  have htwo : (2 : ℚ) < (l.value : ℚ) := by
    exact_mod_cast htwoNat
  have hinv_two : (l.value : ℚ)⁻¹ < (2 : ℚ)⁻¹ := by
    exact (inv_lt_inv₀ hpos (by norm_num : (0 : ℚ) < 2)).2 htwo
  have hinv : (l.value : ℚ)⁻¹ < 1 :=
    hinv_two.trans (two_inv_lt_one (α := ℚ))
  norm_num [sourceTypeOneLTorsionPlusMinus, Iut.OrbicurveSignature.IsHyperbolic,
    Iut.OrbicurveSignature.eulerCharacteristic]
  linarith

structure SourceOncePuncturedGeometry
    {F : Type u} [Field F]
    (curve : PuncturedEllipticCurve F)
    (X : Iut.HyperbolicOrbicurve F) where
  signature : X.signature = sourceTypeOneOne

namespace SourceOncePuncturedGeometry

variable {F : Type u} [Field F]
variable {curve : PuncturedEllipticCurve F}
variable {X : Iut.HyperbolicOrbicurve F}

theorem signature_spec (G : SourceOncePuncturedGeometry curve X) :
    X.signature = sourceTypeOneOne :=
  G.signature

theorem signature_eq_oncePuncturedElliptic
    (G : SourceOncePuncturedGeometry curve X) :
    X.signature = Iut.OrbicurveSignature.oncePuncturedElliptic := by
  calc
    X.signature = sourceTypeOneOne := G.signature
    _ = Iut.OrbicurveSignature.oncePuncturedElliptic := by
      apply Iut.OrbicurveSignature.ext <;> rfl

theorem signature_is_hyperbolic
    (G : SourceOncePuncturedGeometry curve X) :
    X.signature.IsHyperbolic := by
  rw [G.signature]
  exact sourceTypeOneOne_hyperbolic

theorem curve_jInvariant_spec
    (_G : SourceOncePuncturedGeometry curve X) :
    curve.jInvariant = curve.curve.j :=
  curve.jInvariant_spec

end SourceOncePuncturedGeometry

structure SourceFieldOfModuli
    (A : InitialThetaArithmeticData l) where
  jModuli : A.Fmod
  algebraMap_jModuli :
    algebraMap A.Fmod A.F jModuli = A.curve.jInvariant

namespace SourceFieldOfModuli

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData l}

theorem algebraMap_jInvariant_spec (M : SourceFieldOfModuli A) :
    algebraMap A.Fmod A.F M.jModuli = A.curve.jInvariant :=
  M.algebraMap_jModuli

theorem algebraMap_curve_j_spec (M : SourceFieldOfModuli A) :
    algebraMap A.Fmod A.F M.jModuli = A.curve.curve.j := by
  calc
    algebraMap A.Fmod A.F M.jModuli = A.curve.jInvariant :=
      M.algebraMap_jModuli
    _ = A.curve.curve.j := A.curve.jInvariant_spec

theorem jInvariant_mem_algebraMap_range (M : SourceFieldOfModuli A) :
    A.curve.jInvariant ∈ Set.range (algebraMap A.Fmod A.F) := by
  exact ⟨M.jModuli, M.algebraMap_jModuli⟩

end SourceFieldOfModuli

def isFiniteSolvableGaloisSubextension
    {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar]
    (E : IntermediateField k kbar) : Prop :=
  FiniteDimensional k E ∧ IsGalois k E ∧ IsSolvable (E ≃ₐ[k] E)

/-
  The predicate above is only a source condition.  In particular, it does not
  define the maximal solvable extension by a generic lattice construction: the
  source contract must supply an actual intermediate field and prove both that it is
  finite/Galois/solvable and that it contains every qualifying subextension.
  Those two fields are kept explicitly in `SourceClauseA` below.  No generic
  maximal-extension constructor is available here, because the required
  closure and source identification are not proved by the imported foundations.
-/

noncomputable def schemeRestrictScalars
    (F K : Type u) [Field F] [Field K] [Algebra F K] :
    SchemeOverField K ⥤ SchemeOverField F :=
  Over.map (Spec.map (CommRingCat.ofHom (algebraMap F K)))

noncomputable def schemeRestrictScalarsPseudofunctor
    (F K : Type u) [Field F] [Field K] [Algebra F K] :
    LocallyDiscrete (SchemeOverField K)ᵒᵖ ⥤ᵖ
      LocallyDiscrete (SchemeOverField F)ᵒᵖ :=
  (schemeRestrictScalars F K).op.toPseudofunctor

structure SourceEtaleStackScalarExtension
    (F K : Type u) [Field F] [Field K] [Algebra F K]
    (X : EtaleStackOverField F) where
  result : EtaleStackOverField K
  fiberEquivalence :
    Bicategory.Equivalence result.fiber
      (Pseudofunctor.comp
        (schemeRestrictScalarsPseudofunctor F K) X.fiber)

structure SourceOrbicurveScalarExtension
    (F K : Type u) [Field F] [Field K] [Algebra F K]
    (X : Iut.HyperbolicOrbicurve F) where
  result : Iut.HyperbolicOrbicurve K
  stackExtension : SourceEtaleStackScalarExtension F K X.stack
  target_stack : result.stack = stackExtension.result
  genus_preserved : result.signature.genus = X.signature.genus
  stackyOrders_preserved : result.signature.stackyOrders = X.signature.stackyOrders
  punctures_preserved : result.signature.punctures = X.signature.punctures

theorem SourceOrbicurveScalarExtension.signature_preserved
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    {X : Iut.HyperbolicOrbicurve F}
    (E : SourceOrbicurveScalarExtension F K X) :
    E.result.signature = X.signature := by
  apply Iut.OrbicurveSignature.ext
  · exact E.genus_preserved
  · exact E.stackyOrders_preserved
  · exact E.punctures_preserved

structure SourceOrbicurveMorphismScalarExtension
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    {X Y : Iut.HyperbolicOrbicurve F}
    (Xext : SourceOrbicurveScalarExtension F K X)
    (Yext : SourceOrbicurveScalarExtension F K Y)
    (f : X.Hom Y) where
  result : Xext.result.Hom Yext.result
  restrictedMap :
    Pseudofunctor.StrongTrans
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor F K) X.stack.fiber)
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor F K) Y.stack.fiber)
  restrictedMap_app : ∀ S,
    restrictedMap.app S = f.app ((schemeRestrictScalarsPseudofunctor F K).obj S)

structure SourceOrbicurveSquare
    {F : Type u} [Field F]
    (P X Y Z : Iut.HyperbolicOrbicurve F) where
  toX : P.Hom X
  toY : P.Hom Y
  xToBase : X.Hom Z
  yToBase : Y.Hom Z
  commutes : Iut.HyperbolicOrbicurve.Hom.TwoIso
    (Iut.HyperbolicOrbicurve.Hom.comp toX xToBase)
    (Iut.HyperbolicOrbicurve.Hom.comp toY yToBase)

/- A genuine finite-etale cover and its profinite exact sequence.  The
   geometric group is derived as the kernel of the actual projection. -/
structure SourceOrbicurveGroupData
    {F : Type u} [Field F]
    (X : Iut.HyperbolicOrbicurve F)
    (G : ProfiniteGrp.{u}) where
  groups : Iut.OrbicurveFundamentalGroupData X G

/- A finite-etale cover whose source and target orbicurves are fixed in the
   type.  This is the dependent shape of the printed map `X_K -> C_K`:
   unlike `Iut.OrbicurveFiniteEtaleCover`, whose source is an existential
   etale stack, this record cannot later be assigned an unrelated source and
   therefore needs no equality transport before its map is compared with the
   quotient morphism. -/
structure SourceOrbicurveFiniteEtaleCover
    {F : Type u} [Field F]
    (source target : Iut.HyperbolicOrbicurve F) where
  map : source.Hom target
  finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map

namespace SourceOrbicurveFiniteEtaleCover

variable {F : Type u} [Field F]
variable {source target : Iut.HyperbolicOrbicurve F}

def map_is_finite_etale
    (cover : SourceOrbicurveFiniteEtaleCover source target) :
    Iut.EtaleStackFiniteEtaleMorphism cover.map :=
  cover.finiteEtale

end SourceOrbicurveFiniteEtaleCover

namespace SourceOrbicurveGroupData

variable {F : Type u} [Field F]
variable {X : Iut.HyperbolicOrbicurve F}
variable {G : ProfiniteGrp.{u}}

abbrev sequence (D : SourceOrbicurveGroupData X G) :=
  D.groups.exactSequence

theorem projection_surjective (D : SourceOrbicurveGroupData X G) :
    Function.Surjective D.sequence.projection :=
  D.groups.projection_surjective

theorem inclusion_injective (D : SourceOrbicurveGroupData X G) :
    Function.Injective D.sequence.inclusion :=
  D.sequence.inclusion_injective

end SourceOrbicurveGroupData

/- The full sign quotient package, with actual stack maps and universal
   property.  No point-set carrier is introduced. -/
structure SourceSignQuotientData
    (A : InitialThetaArithmeticData l) where
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
  /- The remaining three entries are the literal tuple components in
     Definition 3.1(e)-(f).  They are dependent on the supplied orbicurves
     and are not reconstructed from the arithmetic record. -/
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
      NumberFieldPlace.comap (k := A.Fmod) v.1 =
        (V_mod_bijection.symm v)
  epsilon : Iut.OrbicurveBoundaryCusp cK

theorem sourceFbar_spec (_S : SourceSignQuotientData A) :
    IsAlgClosed (SourceFbar A) := inferInstance

theorem sourceFbar_elements_algebraic (_S : SourceSignQuotientData A)
    (x : SourceFbar A) : IsAlgebraic A.F x :=
  Algebra.IsAlgebraic.isAlgebraic x

theorem sourceAbsoluteGalois_spec (_S : SourceSignQuotientData A) :
    SourceAbsoluteGalois A =
      (AlgebraicClosure A.F ≃ₐ[A.F] AlgebraicClosure A.F) := rfl

namespace SourceSignQuotientData

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

theorem xF_once_punctured (S : SourceSignQuotientData A) :
    S.xF.signature = Iut.OrbicurveSignature.oncePuncturedElliptic := by
  exact S.xF_geometry.signature

theorem xK_signature (S : SourceSignQuotientData A) :
    S.xK.signature = S.xF.signature := by
  rw [S.xK_eq_extension]
  exact SourceOrbicurveScalarExtension.signature_preserved S.xKExtension

theorem cK_signature (S : SourceSignQuotientData A) :
    S.cK.signature = S.cF.signature := by
  rw [S.cK_eq_extension]
  exact SourceOrbicurveScalarExtension.signature_preserved S.cKExtension

theorem selected_places_spec (S : SourceSignQuotientData A) :
    S.V = S.V_section.selected := S.V_eq_section

def V_mod (A : InitialThetaArithmeticData l) : Set (NumberFieldPlace A.Fmod) :=
  Set.univ

theorem V_mod_eq_univ (A : InitialThetaArithmeticData l) :
    V_mod A = Set.univ := rfl

/- The source defines the complementary moduli-place set from the supplied
   bad set; it is not an independently chosen carrier. -/
def V_mod_good (S : SourceSignQuotientData A) :
    Set (NumberFieldPlace A.Fmod) :=
  V_mod A \ (NumberFieldPlace.finite '' S.V_mod_bad)

theorem V_mod_good_eq_compl_bad (S : SourceSignQuotientData A) :
    V_mod_good S = (NumberFieldPlace.finite '' S.V_mod_bad)ᶜ := by
  ext p
  simp [V_mod_good, V_mod]

theorem V_mod_bad_or_good_cover (S : SourceSignQuotientData A) :
    NumberFieldPlace.finite '' S.V_mod_bad ∪ V_mod_good S = V_mod A := by
  rw [V_mod_good_eq_compl_bad S, V_mod_eq_univ]
  exact Set.union_compl_self _

theorem V_mod_bad_or_good_disjoint (S : SourceSignQuotientData A) :
    Disjoint (NumberFieldPlace.finite '' S.V_mod_bad) (V_mod_good S) := by
  rw [V_mod_good_eq_compl_bad S]
  rw [Set.disjoint_left]
  intro p hpbad hpgood
  exact hpgood hpbad

theorem bad_moduli_places_subset (_S : SourceSignQuotientData A) :
    ∀ p : NumberField.FinitePlace A.Fmod,
      NumberFieldPlace.finite p ∈ V_mod A := by
  intro p
  trivial

theorem bad_residue_characteristic_odd (S : SourceSignQuotientData A)
    (p : NumberField.FinitePlace A.Fmod) (hp : p ∈ S.V_mod_bad) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  S.V_mod_bad_odd_residue_characteristic p hp

/-!
  `V_F_non` records the finite places of `F` lying below the selected finite
  places of `V ⊆ V(K)`.  It is useful for the later selected-place clauses,
  but it is not the carrier of Definition 3.1(a): the source writes
  `V(F)^non`, which is the full set of nonarchimedean places of `F` (IUT I,
  §0 and Definition 3.1(b)).
-/
def V_F_non (S : SourceSignQuotientData A) :
    Set (NumberField.FinitePlace A.F) :=
  {p | ∃ (w : NumberField.FinitePlace A.K)
      (_hw : NumberFieldPlace.finite w ∈ S.V),
      NumberFieldFinitePlace.comap (k := A.F) w = p}

theorem V_F_non_spec (S : SourceSignQuotientData A)
    (p : NumberField.FinitePlace A.F) :
    p ∈ V_F_non S ↔
      ∃ (w : NumberField.FinitePlace A.K)
        (_hw : NumberFieldPlace.finite w ∈ S.V),
        NumberFieldFinitePlace.comap (k := A.F) w = p :=
  Iff.rfl

def V_F_nonarchimedean
  (A : InitialThetaArithmeticData l) : Set (NumberField.FinitePlace A.F) :=
  Set.univ

theorem V_F_nonarchimedean_eq_univ (A : InitialThetaArithmeticData l) :
    V_F_nonarchimedean A = Set.univ :=
  rfl

theorem V_F_nonarchimedean_spec (A : InitialThetaArithmeticData l)
    (p : NumberField.FinitePlace A.F) :
    p ∈ V_F_nonarchimedean A := by
  trivial

def V_F_bad (S : SourceSignQuotientData A) :
    Set (NumberFieldPlace A.F) :=
  {v | NumberFieldPlace.comap (k := A.Fmod) v ∈
    NumberFieldPlace.finite '' S.V_mod_bad}

def V_F_good (S : SourceSignQuotientData A) :
    Set (NumberFieldPlace A.F) :=
  {v | NumberFieldPlace.comap (k := A.Fmod) v ∈ V_mod_good S}

theorem V_F_bad_or_good_cover (S : SourceSignQuotientData A) :
    V_F_bad S ∪ V_F_good S = Set.univ := by
  apply Set.Subset.antisymm
  · intro v _
    trivial
  · intro v _
    by_cases h : NumberFieldPlace.comap (k := A.Fmod) v ∈
        NumberFieldPlace.finite '' S.V_mod_bad
    · left
      change NumberFieldPlace.comap (k := A.Fmod) v ∈
        NumberFieldPlace.finite '' S.V_mod_bad
      exact h
    · right
      change NumberFieldPlace.comap (k := A.Fmod) v ∈ V_mod_good S
      rw [V_mod_good_eq_compl_bad S]
      exact h

theorem V_F_bad_or_good_disjoint (S : SourceSignQuotientData A) :
    Disjoint (V_F_bad S) (V_F_good S) := by
  rw [Set.disjoint_left]
  intro v hvbad hvgood
  change NumberFieldPlace.comap (k := A.Fmod) v ∈
    NumberFieldPlace.finite '' S.V_mod_bad at hvbad
  have hgood : NumberFieldPlace.comap (k := A.Fmod) v ∉
      NumberFieldPlace.finite '' S.V_mod_bad := by
    simpa [V_F_good, V_mod_good, V_mod] using hvgood
  exact hgood hvbad

theorem V_F_bad_finite_spec (S : SourceSignQuotientData A)
    (p : NumberField.FinitePlace A.F) :
    NumberFieldPlace.finite p ∈ V_F_bad S ↔
    NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad := by
  simp [V_F_bad]

def V_non (S : SourceSignQuotientData A) :
    Set {v : NumberFieldPlace A.K // v ∈ S.V} :=
  {v | NumberFieldPlace.IsFinite v.1}

def V_arc (S : SourceSignQuotientData A) :
    Set {v : NumberFieldPlace A.K // v ∈ S.V} :=
  {v | NumberFieldPlace.IsInfinite v.1}

def V_mod_place (S : SourceSignQuotientData A)
    (v : {v : NumberFieldPlace A.K // v ∈ S.V}) :
    NumberFieldPlace A.Fmod :=
  S.V_mod_bijection.symm v

def V_bad (S : SourceSignQuotientData A) :
    Set {v : NumberFieldPlace A.K // v ∈ S.V} :=
  {v | V_mod_place S v ∈ NumberFieldPlace.finite '' S.V_mod_bad}

def V_good (S : SourceSignQuotientData A) :
    Set {v : NumberFieldPlace A.K // v ∈ S.V} :=
  {v | V_mod_place S v ∉ NumberFieldPlace.finite '' S.V_mod_bad}

theorem V_non_or_arc_cover (S : SourceSignQuotientData A) :
    V_non S ∪ V_arc S = Set.univ := by
  ext v
  cases v with
  | mk place hplace =>
      cases place with
      | finite w => simp [V_non, V_arc]
      | infinite w => simp [V_non, V_arc]

theorem V_non_or_arc_disjoint (S : SourceSignQuotientData A) :
    Disjoint (V_non S) (V_arc S) := by
  rw [Set.disjoint_left]
  intro v hvnon hvarc
  rcases v with ⟨place, hplace⟩
  change NumberFieldPlace.IsFinite place at hvnon
  change NumberFieldPlace.IsInfinite place at hvarc
  cases place with
  | finite w => exact NumberFieldPlace.not_isInfinite_finite w hvarc
  | infinite w => exact NumberFieldPlace.not_isFinite_infinite w hvnon

theorem V_bad_or_good_cover (S : SourceSignQuotientData A) :
    V_bad S ∪ V_good S = Set.univ := by
  apply Set.Subset.antisymm
  · intro v _
    trivial
  · intro v _
    by_cases h : V_mod_place S v ∈
        NumberFieldPlace.finite '' S.V_mod_bad
    · left
      change V_mod_place S v ∈ NumberFieldPlace.finite '' S.V_mod_bad
      exact h
    · right
      change V_mod_place S v ∉ NumberFieldPlace.finite '' S.V_mod_bad
      exact h

theorem V_bad_or_good_disjoint (S : SourceSignQuotientData A) :
    Disjoint (V_bad S) (V_good S) := by
  rw [Set.disjoint_left]
  intro v hvbad hvgood
  exact hvgood hvbad

noncomputable def selected_places_equiv (S : SourceSignQuotientData A) :
    NumberFieldPlace A.Fmod ≃ {v : NumberFieldPlace A.K // v ∈ S.V} :=
  S.V_mod_bijection

theorem selected_places_comap (S : SourceSignQuotientData A)
    (v : {v : NumberFieldPlace A.K // v ∈ S.V}) :
    NumberFieldPlace.comap (k := A.Fmod) v.1 = S.V_mod_bijection.symm v :=
  S.V_place_comap v

noncomputable def epsilon_spec (S : SourceSignQuotientData A) :
    Iut.OrbicurveBoundaryCusp S.cK := S.epsilon

end SourceSignQuotientData

/-! ## Clause (a): field, curve, and solvable extension -/

structure SourceClauseA (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) where
  stable_reduction_nonarchimedean :
    ∀ p : NumberField.FinitePlace A.F,
      A.curve.HasStableReductionAt p
  field_of_moduli : SourceFieldOfModuli A
  maximal_solvable_extension :
    IntermediateField A.Fmod A.F
  maximal_solvable_property :
    isFiniteSolvableGaloisSubextension maximal_solvable_extension
  maximal_solvable_contains :
    ∀ E : IntermediateField A.Fmod A.F,
      isFiniteSolvableGaloisSubextension E →
        E ≤ maximal_solvable_extension

namespace SourceClauseA

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A}

theorem sqrtNegOne_spec (_C : SourceClauseA A S) : HasSqrtNegOne A.F :=
  A.tower.sqrtNegOne
theorem stable_spec (C : SourceClauseA A S)
    (p : NumberField.FinitePlace A.F) :
    A.curve.HasStableReductionAt p :=
  C.stable_reduction_nonarchimedean p
theorem field_moduli_spec (C : SourceClauseA A S) :
    ∃ jModuli : A.Fmod, algebraMap A.Fmod A.F jModuli = A.curve.jInvariant :=
  ⟨C.field_of_moduli.jModuli, C.field_of_moduli.algebraMap_jModuli⟩
theorem degree_spec (_C : SourceClauseA A S) :
    Nat.Coprime (Module.finrank A.Fmod A.F) l.value :=
  A.tower.degreePrimeToL

theorem maximal_solvable_finite (C : SourceClauseA A S) :
    FiniteDimensional A.Fmod C.maximal_solvable_extension :=
  C.maximal_solvable_property.1

theorem maximal_solvable_galois (C : SourceClauseA A S) :
    IsGalois A.Fmod C.maximal_solvable_extension :=
  C.maximal_solvable_property.2.1

theorem maximal_solvable_group (C : SourceClauseA A S) :
    IsSolvable (C.maximal_solvable_extension ≃ₐ[A.Fmod]
      C.maximal_solvable_extension) :=
  C.maximal_solvable_property.2.2

theorem fmod_galois_spec (_C : SourceClauseA A S) : IsGalois A.Fmod A.F :=
  inferInstance

theorem f_galois_k_spec (_C : SourceClauseA A S) : IsGalois A.F A.K :=
  inferInstance

theorem fbar_algebraic_spec (_C : SourceClauseA A S)
    (x : SourceFbar A) : IsAlgebraic A.F x :=
  Algebra.IsAlgebraic.isAlgebraic x

theorem fbar_algClosed_spec (_C : SourceClauseA A S) :
    IsAlgClosed (SourceFbar A) := inferInstance

end SourceClauseA

/-! ## Clause (b): bad places and actual Tate comparisons -/

structure SourceTateComparisonWitness
    (A : InitialThetaArithmeticData l)
    (p : NumberField.FinitePlace A.F) where
  parameter : NumberFieldFinitePlace.FinitePlaceQCandidate p
  comparison : TateCurveComparison A.curve p parameter
  order_coprime : Nat.Coprime parameter.order l.value

structure SourceClauseB (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A)
    (C : SourceClauseA A S) where
  multiplicative_over_bad :
    ∀ p : NumberField.FinitePlace A.F,
      NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad →
      A.curve.HasMultiplicativeReductionAt p
  q_comparison :
    ∀ (p : NumberField.FinitePlace A.F)
      (_hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad),
      Nonempty (SourceTateComparisonWitness A p)
  residue_characteristic_prime_to_l :
    ∀ (p : NumberField.FinitePlace A.F)
      (_hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad),
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := A.Fmod) p))

theorem bad_moduli_subset_moduli
    (_B : SourceClauseB A S C)
    (p : NumberField.FinitePlace A.Fmod)
    (_hp : p ∈ S.V_mod_bad) :
    NumberFieldPlace.finite p ∈ SourceSignQuotientData.V_mod A := by
  exact SourceSignQuotientData.bad_moduli_places_subset S p

namespace SourceClauseB

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A} {C : SourceClauseA A S}

theorem bad_nonempty_spec (_B : SourceClauseB A S C) :
    S.V_mod_bad.Nonempty := S.V_mod_bad_nonempty

theorem multiplicative_spec (B : SourceClauseB A S C)
    (p : NumberField.FinitePlace A.F)
    (hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad) :
    A.curve.HasMultiplicativeReductionAt p :=
  B.multiplicative_over_bad p hp

theorem q_comparison_spec (B : SourceClauseB A S C)
    (p : NumberField.FinitePlace A.F)
    (hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad) :
    Nonempty (SourceTateComparisonWitness A p) := B.q_comparison p hp

end SourceClauseB

/-! ## Clause (c): torsion representation and kernel field -/

structure SourceClauseC (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A)
    (C : SourceClauseA A S)
    (B : SourceClauseB A S C) where
  torsion23_rational : PuncturedEllipticCurve.Torsion23Rational A.curve
  torsion_basis :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l
  /- The K/F carrier comparison is constructed from the actual finite field
     extension and the two algebraic closures.  Clause (f)'s K-side basis is
     therefore derived from this transport and the source-supplied F-side
     basis; it is not an unrelated carrier or an extra axiom. -/
  representation :
    (SourceAbsoluteGalois A) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)
  representation_eq_canonical :
    representation = A.curve.galoisLTorsionMatrixRepresentation l torsion_basis
  image_contains_SL2 :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      representation.range
  kernel_field_identification :
    A.K ≃ₐ[A.F]
      A.curve.galoisLTorsionKernelField l torsion_basis
  kernel_field_identification_range :
    Set.range (fun x : A.K =>
      (kernel_field_identification x : AlgebraicClosure A.F)) =
      (A.curve.galoisLTorsionKernelField l torsion_basis : Set (AlgebraicClosure A.F))

namespace SourceClauseC

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A} {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}

noncomputable def k_to_f_torsion_transport
    (_D : SourceClauseC A S C B) :
    (A.curve.baseChange A.K).LTorsion l ≃ₗ[ZMod l.value]
      A.curve.LTorsion l :=
  InitialThetaSource.PuncturedEllipticCurve.initialThetaKToFTorsionTransport A

noncomputable def k_torsion_basis
    (D : SourceClauseC A S C B) :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      (A.curve.baseChange A.K).LTorsion l :=
  D.torsion_basis.trans D.k_to_f_torsion_transport.symm

theorem k_torsion_basis_transport_eq_f_torsion_basis
    (D : SourceClauseC A S C B) :
    D.k_torsion_basis.trans D.k_to_f_torsion_transport = D.torsion_basis := by
  apply LinearEquiv.ext
  intro x
  simp [k_torsion_basis]

theorem torsion_spec (D : SourceClauseC A S C B) :
    PuncturedEllipticCurve.Torsion23Rational A.curve := D.torsion23_rational

noncomputable def k_torsion_basis_spec (D : SourceClauseC A S C B) :
    (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      (A.curve.baseChange A.K).LTorsion l :=
  D.k_torsion_basis

noncomputable def k_to_f_torsion_transport_spec (D : SourceClauseC A S C B) :
    (A.curve.baseChange A.K).LTorsion l ≃ₗ[ZMod l.value]
      A.curve.LTorsion l :=
  D.k_to_f_torsion_transport

theorem k_torsion_basis_transport_spec (D : SourceClauseC A S C B) :
    D.k_torsion_basis.trans D.k_to_f_torsion_transport = D.torsion_basis :=
  by
  apply LinearEquiv.ext
  intro x
  simp [k_torsion_basis]

theorem image_spec (D : SourceClauseC A S C B) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      D.representation.range :=
  D.image_contains_SL2

theorem representation_continuous (D : SourceClauseC A S C B) :
    Continuous D.representation := by
  rw [D.representation_eq_canonical]
  exact A.curve.galoisLTorsionMatrixRepresentation_continuous l D.torsion_basis

theorem kernel_field_finite_galois (_D : SourceClauseC A S C B) :
    IsGalois A.F A.K :=
  inferInstance

theorem kernel_field_range_spec (D : SourceClauseC A S C B) :
    Set.range (fun x : A.K =>
      (D.kernel_field_identification x : AlgebraicClosure A.F)) =
      (A.curve.galoisLTorsionKernelField l D.torsion_basis :
        Set (AlgebraicClosure A.F)) :=
  D.kernel_field_identification_range

end SourceClauseC

/-! ## Clause (d): actual K orbicurves, covers, and fundamental groups -/

structure SourceClauseD (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A)
    (C : SourceClauseA A S)
    (B : SourceClauseB A S C)
    (D : SourceClauseC A S C B) where
  k_signAction : Iut.OrbicurveSignAction S.xK
  k_quotient : Iut.OrbicurveSignInvariantMorphism k_signAction S.cK
  k_quotientWitness : Iut.OrbicurveSignQuotientWitness k_signAction k_quotient
  k_quotientExtension : SourceOrbicurveMorphismScalarExtension
    S.xKExtension S.cKExtension S.quotient.map
  k_quotient_map_eq_extension :
    k_quotient.map = Iut.HyperbolicOrbicurve.Hom.cast
      S.xK_eq_extension.symm S.cK_eq_extension.symm
      k_quotientExtension.result
  k_l_torsion_cover : SourceOrbicurveFiniteEtaleCover S.xK S.cK
  k_l_torsion_cover_map_eq_quotient :
    k_l_torsion_cover.map = k_quotient.map
  x_groups : SourceOrbicurveGroupData S.xK (Iut.AbsoluteGaloisProfinite A.K)
  c_groups : SourceOrbicurveGroupData S.cK (Iut.AbsoluteGaloisProfinite A.K)
  group_inclusion :
    Iut.ProfiniteFundamentalGroupInclusion
      x_groups.sequence.geometric x_groups.sequence.arithmetic
      c_groups.sequence.geometric c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      x_groups.sequence c_groups.sequence
  x_to_F_groups :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      x_groups.sequence.geometric x_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      S.xFGroups.sequence.geometric S.xFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.F)
      x_groups.sequence S.xFGroups.sequence
  c_to_F_groups :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      c_groups.sequence.geometric c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      S.cFGroups.sequence.geometric S.cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.F)
      c_groups.sequence S.cFGroups.sequence

namespace SourceClauseD

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A} {C : SourceClauseA A S}
variable {B : SourceClauseB A S C} (D : SourceClauseC A S C B)

theorem groups_have_exact_projection
    (E : SourceClauseD A S C B D) :
    Function.Surjective E.x_groups.sequence.projection ∧
      Function.Surjective E.c_groups.sequence.projection :=
  ⟨E.x_groups.projection_surjective, E.c_groups.projection_surjective⟩

end SourceClauseD

/-!
  The local records below are indexed by the actual selected place.  Their
  local field is the corresponding Mathlib completion, their orbicurves are
  supplied as scalar extensions over that completion, and their fundamental
  groups are independent local objects.  The only global data appearing in a
  local record are the target exact sequences and the certified embeddings
  into them.  Thus a local diagram cannot be witnessed by reusing the global
  exact sequence itself.
-/

noncomputable def sourceFiniteLocalCurve
    (A : InitialThetaArithmeticData l)
    (w : NumberField.FinitePlace A.K) :
    PuncturedEllipticCurve (NumberFieldFinitePlace.Completion w) :=
  A.curve.map
    ((algebraMap A.K (NumberFieldFinitePlace.Completion w)).comp
      (algebraMap A.F A.K))

noncomputable def sourceInfiniteLocalCurve
    (A : InitialThetaArithmeticData l)
    (w : NumberField.InfinitePlace A.K) :
    PuncturedEllipticCurve w.Completion :=
  A.curve.map
    ((algebraMap A.K w.Completion).comp (algebraMap A.F A.K))

def selectedFinitePlace
    {A : InitialThetaArithmeticData l}
    {v : NumberFieldPlace A.K}
    (hv : NumberFieldPlace.IsFinite v) :
    NumberField.FinitePlace A.K :=
  match v with
  | .finite w => w
  | .infinite _w => False.elim hv

def selectedInfinitePlace
    {A : InitialThetaArithmeticData l}
    {v : NumberFieldPlace A.K}
    (hv : NumberFieldPlace.IsInfinite v) :
    NumberField.InfinitePlace A.K :=
  match v with
  | .finite _w => False.elim hv
  | .infinite w => w

noncomputable def sourceKQuotientMap
    {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S}
    {B : SourceClauseB A S C}
    {D : SourceClauseC A S C B}
    (E : SourceClauseD A S C B D) : S.xK.Hom S.cK :=
  E.k_quotient.map

structure SourceFiniteLocalSource
    (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A)
    (C : SourceClauseA A S)
    (B : SourceClauseB A S C)
    (D : SourceClauseC A S C B)
    (E : SourceClauseD A S C B D)
    (w : NumberField.FinitePlace A.K) where
  localCurve : PuncturedEllipticCurve (NumberFieldFinitePlace.Completion w)
  local_curve_eq_actual : localCurve = sourceFiniteLocalCurve A w
  xExtension :
    SourceOrbicurveScalarExtension A.K
      (NumberFieldFinitePlace.Completion w) S.xK
  cExtension :
    SourceOrbicurveScalarExtension A.K
      (NumberFieldFinitePlace.Completion w) S.cK
  signAction : Iut.OrbicurveSignAction xExtension.result
  quotientMapExtension :
    SourceOrbicurveMorphismScalarExtension
      xExtension cExtension (sourceKQuotientMap E)
  quotient :
    Iut.OrbicurveSignInvariantMorphism signAction cExtension.result
  quotient_map_eq_extension : quotient.map = quotientMapExtension.result
  quotientWitness :
    Iut.OrbicurveSignQuotientWitness signAction quotient
  xGroups :
    SourceOrbicurveGroupData xExtension.result
      (Iut.AbsoluteGaloisProfinite
        (NumberFieldFinitePlace.Completion w))
  cGroups :
    SourceOrbicurveGroupData cExtension.result
      (Iut.AbsoluteGaloisProfinite
        (NumberFieldFinitePlace.Completion w))
  local_group_inclusion :
    Iut.ProfiniteFundamentalGroupInclusion
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite
        (NumberFieldFinitePlace.Completion w))
      xGroups.sequence cGroups.sequence
  xGlobalEmbedding :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite
        (NumberFieldFinitePlace.Completion w))
      E.x_groups.sequence.geometric E.x_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      xGroups.sequence E.x_groups.sequence
  cGlobalEmbedding :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite
        (NumberFieldFinitePlace.Completion w))
      E.c_groups.sequence.geometric E.c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      cGroups.sequence E.c_groups.sequence
  galois_embedding_agreement :
    xGlobalEmbedding.galois.hom = cGlobalEmbedding.galois.hom

namespace SourceFiniteLocalSource

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A} {C : SourceClauseA A S}
variable {B : SourceClauseB A S C} {D : SourceClauseC A S C B}
variable {E : SourceClauseD A S C B D}
variable {w : NumberField.FinitePlace A.K}

abbrev localField
    (_L : SourceFiniteLocalSource A S C B D E w) :=
  NumberFieldFinitePlace.Completion w

abbrev xLocal
    (L : SourceFiniteLocalSource A S C B D E w) :=
  L.xExtension.result

abbrev cLocal
    (L : SourceFiniteLocalSource A S C B D E w) :=
  L.cExtension.result

theorem local_curve_is_actual_base_change :
    sourceFiniteLocalCurve A w =
      A.curve.map
        ((algebraMap A.K (NumberFieldFinitePlace.Completion w)).comp
          (algebraMap A.F A.K)) :=
  rfl

theorem x_groups_projection_surjective
    (L : SourceFiniteLocalSource A S C B D E w) :
    Function.Surjective L.xGroups.sequence.projection :=
  L.xGroups.projection_surjective

theorem c_groups_projection_surjective
    (L : SourceFiniteLocalSource A S C B D E w) :
    Function.Surjective L.cGroups.sequence.projection :=
  L.cGroups.projection_surjective

theorem x_groups_inclusion_injective
    (L : SourceFiniteLocalSource A S C B D E w) :
    Function.Injective L.xGroups.sequence.inclusion :=
  L.xGroups.inclusion_injective

theorem c_groups_inclusion_injective
    (L : SourceFiniteLocalSource A S C B D E w) :
    Function.Injective L.cGroups.sequence.inclusion :=
  L.cGroups.inclusion_injective

theorem galois_embedding_agreement_spec
    (L : SourceFiniteLocalSource A S C B D E w) :
    L.xGlobalEmbedding.galois.hom = L.cGlobalEmbedding.galois.hom :=
  L.galois_embedding_agreement

end SourceFiniteLocalSource

structure SourceInfiniteLocalSource
    (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A)
    (C : SourceClauseA A S)
    (B : SourceClauseB A S C)
    (D : SourceClauseC A S C B)
    (E : SourceClauseD A S C B D)
    (w : NumberField.InfinitePlace A.K) where
  localCurve : PuncturedEllipticCurve w.Completion
  local_curve_eq_actual : localCurve = sourceInfiniteLocalCurve A w
  xExtension :
    SourceOrbicurveScalarExtension A.K w.Completion S.xK
  cExtension :
    SourceOrbicurveScalarExtension A.K w.Completion S.cK
  signAction : Iut.OrbicurveSignAction xExtension.result
  quotientMapExtension :
    SourceOrbicurveMorphismScalarExtension
      xExtension cExtension (sourceKQuotientMap E)
  quotient :
    Iut.OrbicurveSignInvariantMorphism signAction cExtension.result
  quotient_map_eq_extension : quotient.map = quotientMapExtension.result
  quotientWitness :
    Iut.OrbicurveSignQuotientWitness signAction quotient
  xGroups :
    SourceOrbicurveGroupData xExtension.result
      (Iut.AbsoluteGaloisProfinite w.Completion)
  cGroups :
    SourceOrbicurveGroupData cExtension.result
      (Iut.AbsoluteGaloisProfinite w.Completion)
  local_group_inclusion :
    Iut.ProfiniteFundamentalGroupInclusion
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite w.Completion)
      xGroups.sequence cGroups.sequence
  xGlobalEmbedding :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite w.Completion)
      E.x_groups.sequence.geometric E.x_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      xGroups.sequence E.x_groups.sequence
  cGlobalEmbedding :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite w.Completion)
      E.c_groups.sequence.geometric E.c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      cGroups.sequence E.c_groups.sequence
  galois_embedding_agreement :
    xGlobalEmbedding.galois.hom = cGlobalEmbedding.galois.hom

namespace SourceInfiniteLocalSource

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A} {C : SourceClauseA A S}
variable {B : SourceClauseB A S C} {D : SourceClauseC A S C B}
variable {E : SourceClauseD A S C B D}
variable {w : NumberField.InfinitePlace A.K}

abbrev localField
    (_L : SourceInfiniteLocalSource A S C B D E w) :=
  w.Completion

abbrev xLocal
    (L : SourceInfiniteLocalSource A S C B D E w) :=
  L.xExtension.result

abbrev cLocal
    (L : SourceInfiniteLocalSource A S C B D E w) :=
  L.cExtension.result

theorem local_curve_is_actual_base_change :
    sourceInfiniteLocalCurve A w =
      A.curve.map
        ((algebraMap A.K w.Completion).comp (algebraMap A.F A.K)) :=
  rfl

theorem x_groups_projection_surjective
    (L : SourceInfiniteLocalSource A S C B D E w) :
    Function.Surjective L.xGroups.sequence.projection :=
  L.xGroups.projection_surjective

theorem c_groups_projection_surjective
    (L : SourceInfiniteLocalSource A S C B D E w) :
    Function.Surjective L.cGroups.sequence.projection :=
  L.cGroups.projection_surjective

theorem x_groups_inclusion_injective
    (L : SourceInfiniteLocalSource A S C B D E w) :
    Function.Injective L.xGroups.sequence.inclusion :=
  L.xGroups.inclusion_injective

theorem c_groups_inclusion_injective
    (L : SourceInfiniteLocalSource A S C B D E w) :
    Function.Injective L.cGroups.sequence.inclusion :=
  L.cGroups.inclusion_injective

theorem galois_embedding_agreement_spec
    (L : SourceInfiniteLocalSource A S C B D E w) :
    L.xGlobalEmbedding.galois.hom = L.cGlobalEmbedding.galois.hom :=
  L.galois_embedding_agreement

end SourceInfiniteLocalSource

/-! ## Clause (e): the literal selected subset and local diagrams -/

structure SourceClauseE (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A)
    (C : SourceClauseA A S)
    (B : SourceClauseB A S C)
    (D : SourceClauseC A S C B)
    (E : SourceClauseD A S C B D) where
  selected_eq_V :
    S.V = S.V_section.selected
  selected_equiv :
    NumberFieldPlace A.Fmod ≃
      {v : NumberFieldPlace A.K // v ∈ S.V}
  finite_local :
    ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
      (hv : v.1.IsFinite),
      SourceFiniteLocalSource A S C B D E
        (selectedFinitePlace hv)
  infinite_local :
    ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
      (hv : v.1.IsInfinite),
      SourceInfiniteLocalSource A S C B D E
        (selectedInfinitePlace hv)

namespace SourceClauseE

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A} {C : SourceClauseA A S}
variable {B : SourceClauseB A S C} {D : SourceClauseC A S C B}
variable {E : SourceClauseD A S C B D}

theorem selected_is_actual_set (L : SourceClauseE A S C B D E) :
    S.V = S.V_section.selected := L.selected_eq_V

noncomputable def selected_equivalence (L : SourceClauseE A S C B D E) :
    NumberFieldPlace A.Fmod ≃
      {v : NumberFieldPlace A.K // v ∈ S.V} :=
  L.selected_equiv

noncomputable def finite_local_spec
    (L : SourceClauseE A S C B D E)
    (v : {v : NumberFieldPlace A.K // v ∈ S.V})
    (hv : v.1.IsFinite) :
    SourceFiniteLocalSource A S C B D E (selectedFinitePlace hv) :=
  L.finite_local v hv

noncomputable def infinite_local_spec
    (L : SourceClauseE A S C B D E)
    (v : {v : NumberFieldPlace A.K // v ∈ S.V})
    (hv : v.1.IsInfinite) :
    SourceInfiniteLocalSource A S C B D E (selectedInfinitePlace hv) :=
  L.infinite_local v hv

noncomputable def finite_local_x_global_embedding
    (L : SourceClauseE A S C B D E)
    (v : {v : NumberFieldPlace A.K // v ∈ S.V})
    (hv : v.1.IsFinite) :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      (L.finite_local v hv).xGroups.sequence.geometric
      (L.finite_local v hv).xGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite
        (NumberFieldFinitePlace.Completion (selectedFinitePlace hv)))
      E.x_groups.sequence.geometric E.x_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      (L.finite_local v hv).xGroups.sequence E.x_groups.sequence :=
  (L.finite_local v hv).xGlobalEmbedding

noncomputable def finite_local_c_global_embedding
    (L : SourceClauseE A S C B D E)
    (v : {v : NumberFieldPlace A.K // v ∈ S.V})
    (hv : v.1.IsFinite) :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      (L.finite_local v hv).cGroups.sequence.geometric
      (L.finite_local v hv).cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite
        (NumberFieldFinitePlace.Completion (selectedFinitePlace hv)))
      E.c_groups.sequence.geometric E.c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      (L.finite_local v hv).cGroups.sequence E.c_groups.sequence :=
  (L.finite_local v hv).cGlobalEmbedding

noncomputable def infinite_local_x_global_embedding
    (L : SourceClauseE A S C B D E)
    (v : {v : NumberFieldPlace A.K // v ∈ S.V})
    (hv : v.1.IsInfinite) :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      (L.infinite_local v hv).xGroups.sequence.geometric
      (L.infinite_local v hv).xGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite
        (selectedInfinitePlace hv).Completion)
      E.x_groups.sequence.geometric E.x_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      (L.infinite_local v hv).xGroups.sequence E.x_groups.sequence :=
  (L.infinite_local v hv).xGlobalEmbedding

noncomputable def infinite_local_c_global_embedding
    (L : SourceClauseE A S C B D E)
    (v : {v : NumberFieldPlace A.K // v ∈ S.V})
    (hv : v.1.IsInfinite) :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      (L.infinite_local v hv).cGroups.sequence.geometric
      (L.infinite_local v hv).cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite
        (selectedInfinitePlace hv).Completion)
      E.c_groups.sequence.geometric E.c_groups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      (L.infinite_local v hv).cGroups.sequence E.c_groups.sequence :=
  (L.infinite_local v hv).cGlobalEmbedding

end SourceClauseE

/-! ## Clause (f): cusp with a source boundary and canonical sign -/

structure SourceClauseF (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A)
    (C : SourceClauseA A S)
    (B : SourceClauseB A S C)
    (D : SourceClauseC A S C B)
    (E : SourceClauseD A S C B D)
    (L : SourceClauseE A S C B D E) where
  /- The boundary datum is tied to the actual K-side torsion module from
     Clause (d).  Its relation to the F-side representation is mediated only
     by the explicit transport supplied in Clause (c). -/
  boundary_origin : TorsionQuotientBoundaryOrigin l A S.cK
  quotient_basis_eq_k_torsion_basis :
    boundary_origin.rank_one_quotient.torsion_basis = D.k_torsion_basis
  boundary_cusp_eq_epsilon :
    boundary_origin.cusp = S.epsilon
  cusp_decomposition :
    Iut.OrbicurveCuspidalDecompositionData E.c_groups.groups
  cusp_decomposition_cusp_eq_origin :
    cusp_decomposition.cusp = boundary_origin.cusp

namespace SourceClauseF

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A} {C : SourceClauseA A S}
variable {B : SourceClauseB A S C} {D : SourceClauseC A S C B}
variable {E : SourceClauseD A S C B D}
variable {L : SourceClauseE A S C B D E}

noncomputable def cusp_spec (F : SourceClauseF A S C B D E L) :
    Iut.OrbicurveBoundaryCusp S.cK := F.boundary_origin.cusp

theorem nonzero_origin_spec (F : SourceClauseF A S C B D E L) :
    ∃ q : F.boundary_origin.rank_one_quotient.Quotient, q ≠ 0 :=
  F.boundary_origin.nonzero_origin_spec

theorem quotient_surjective_spec (F : SourceClauseF A S C B D E L) :
    Function.Surjective F.boundary_origin.rank_one_quotient.quotientMap :=
  F.boundary_origin.quotientMap_surjective

theorem quotient_basis_transport_spec (F : SourceClauseF A S C B D E L) :
    F.boundary_origin.rank_one_quotient.torsion_basis.trans
        D.k_to_f_torsion_transport = D.torsion_basis := by
  rw [F.quotient_basis_eq_k_torsion_basis]
  exact D.k_torsion_basis_transport_eq_f_torsion_basis

theorem quotient_generator_spec (F : SourceClauseF A S C B D E L) :
    F.boundary_origin.rank_one_quotient.quotientEquiv
        F.boundary_origin.rank_one_quotient.distinguishedClass = 1 :=
  F.boundary_origin.distinguishedClass_is_generator

theorem quotient_origin_map_spec (F : SourceClauseF A S C B D E L) :
    F.boundary_origin.originMap F.boundary_origin.distinguishedNonzeroClass =
      F.boundary_origin.cusp :=
  F.boundary_origin.originMap_nonzeroClass_spec

theorem cusp_origin_spec (F : SourceClauseF A S C B D E L) :
    F.boundary_origin.cusp = S.epsilon :=
  F.boundary_cusp_eq_epsilon

end SourceClauseF

/-! ## Complete source datum and the exact dependent quantifier -/

/-! The six entries named in Definition 3.1 are made explicit here.  The
    auxiliary `source` record retains the actual quotient, group, and scalar
    extension objects used by the six clauses; the equalities below ensure
    that the displayed tuple entries and those auxiliary objects are one and
    the same source data.  The algebraic-closure entry is an actual
    `SourceFbarExtension`, not an element of its carrier. -/
structure SourceInitialThetaTuple
    (A : InitialThetaArithmeticData.{u} l) where
  /- The first printed entry `Fbar/F` carries the field and algebraic
     equivalence, rather than selecting one element of `Fbar`. -/
  fbar : SourceFbarExtension A
  source : SourceSignQuotientData A
  xF : Iut.HyperbolicOrbicurve A.F
  xF_eq_source : xF = source.xF
  cK : Iut.HyperbolicOrbicurve A.K
  cK_eq_source : source.cK = cK
  V : Set (NumberFieldPlace A.K)
  V_eq_source : V = source.V
  V_mod_bad : Set (NumberField.FinitePlace A.Fmod)
  V_mod_bad_eq_source : V_mod_bad = source.V_mod_bad
  epsilon : Iut.OrbicurveBoundaryCusp cK
  epsilon_eq_source :
    epsilon = cK_eq_source ▸ source.epsilon

namespace SourceInitialThetaTuple

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

theorem xF_source_eq (T : SourceInitialThetaTuple A) :
    T.xF = T.source.xF := T.xF_eq_source

noncomputable def fbar_comparison (T : SourceInitialThetaTuple A) :
    T.fbar.carrier ≃ₐ[A.F] AlgebraicClosure A.F :=
  T.fbar.comparison

theorem fbar_is_algClosed (T : SourceInitialThetaTuple A) :
    IsAlgClosed T.fbar.carrier :=
  inferInstance

theorem fbar_element_is_algebraic
    (T : SourceInitialThetaTuple A) (x : T.fbar.carrier) :
    IsAlgebraic A.F x :=
  Algebra.IsAlgebraic.isAlgebraic x

theorem cK_source_eq (T : SourceInitialThetaTuple A) :
    T.cK = T.source.cK := T.cK_eq_source.symm

theorem V_source_eq (T : SourceInitialThetaTuple A) :
    T.V = T.source.V := T.V_eq_source

theorem V_mod_bad_source_eq (T : SourceInitialThetaTuple A) :
    T.V_mod_bad = T.source.V_mod_bad := T.V_mod_bad_eq_source

theorem epsilon_source_eq (T : SourceInitialThetaTuple A) :
    T.epsilon = T.cK_eq_source ▸ T.source.epsilon :=
  T.epsilon_eq_source

noncomputable def algebraic_closure_is_canonical
    (T : SourceInitialThetaTuple A) :
    T.fbar.carrier ≃ₐ[A.F] AlgebraicClosure A.F :=
  T.fbar.comparison

theorem complete_source_recovery (T : SourceInitialThetaTuple A) :
    Nonempty (T.fbar.carrier ≃ₐ[A.F] AlgebraicClosure A.F) ∧
      T.xF = T.source.xF ∧
      T.cK = T.source.cK ∧
      T.V = T.source.V ∧
      T.V_mod_bad = T.source.V_mod_bad ∧
      T.epsilon = T.cK_eq_source ▸ T.source.epsilon := by
  exact ⟨⟨T.algebraic_closure_is_canonical⟩, T.xF_source_eq,
    T.cK_source_eq, T.V_source_eq, T.V_mod_bad_source_eq,
    T.epsilon_source_eq⟩

end SourceInitialThetaTuple

structure SourceNativeInitialThetaData (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData.{u} l
  tuple : SourceInitialThetaTuple arithmetic
  clauseA : SourceClauseA arithmetic tuple.source
  clauseB : SourceClauseB arithmetic tuple.source clauseA
  clauseC : SourceClauseC arithmetic tuple.source clauseA clauseB
  clauseD : SourceClauseD arithmetic tuple.source clauseA clauseB clauseC
  clauseE : SourceClauseE arithmetic tuple.source clauseA clauseB clauseC clauseD
  clauseF : SourceClauseF arithmetic tuple.source clauseA clauseB clauseC clauseD clauseE

namespace SourceNativeInitialThetaData

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{u} l)

def clauseA_spec : SourceClauseA T.arithmetic T.tuple.source := T.clauseA
theorem clauseB_spec : SourceClauseB T.arithmetic T.tuple.source T.clauseA := T.clauseB
def clauseC_spec : SourceClauseC T.arithmetic T.tuple.source T.clauseA T.clauseB := T.clauseC
def clauseD_spec : SourceClauseD T.arithmetic T.tuple.source T.clauseA T.clauseB T.clauseC := T.clauseD
def clauseE_spec : SourceClauseE T.arithmetic T.tuple.source T.clauseA T.clauseB T.clauseC T.clauseD := T.clauseE
def clauseF_spec : SourceClauseF T.arithmetic T.tuple.source T.clauseA T.clauseB T.clauseC T.clauseD T.clauseE := T.clauseF

end SourceNativeInitialThetaData

/- The source predicate is the dependent existential in the printed
   Definition 3.1.  The endpoint is a proposition about a supplied six-tuple,
   rather than a theorem asserting that arbitrary arithmetic data has a
   realization. -/
def SourceNativeInitialThetaPredicate
    (A : InitialThetaArithmeticData.{u} l)
    (T : SourceInitialThetaTuple A) : Prop :=
  ∃
    (clauseA : SourceClauseA A T.source)
    (clauseB : SourceClauseB A T.source clauseA)
    (clauseC : SourceClauseC A T.source clauseA clauseB)
    (clauseD : SourceClauseD A T.source clauseA clauseB clauseC)
    (clauseE : SourceClauseE A T.source clauseA clauseB clauseC clauseD)
    (clauseF : SourceClauseF A T.source clauseA clauseB clauseC clauseD clauseE),
    clauseF = clauseF

theorem sourceNativeInitialThetaData_predicate
    (T : SourceNativeInitialThetaData.{u} l) :
    SourceNativeInitialThetaPredicate T.arithmetic T.tuple := by
  exact ⟨T.clauseA, T.clauseB, T.clauseC, T.clauseD, T.clauseE,
    T.clauseF, rfl⟩

def SourceNativeInitialThetaExists (l : PrimeGeFive) : Prop :=
  ∃ (A : InitialThetaArithmeticData.{u} l)
    (T : SourceInitialThetaTuple (A := A)),
    SourceNativeInitialThetaPredicate A T

/-! Paper-facing name for the exact Definition 3.1 proposition. -/
abbrev InitialThetaData (l : PrimeGeFive) : Prop :=
  SourceNativeInitialThetaExists.{u} l

theorem initialThetaData_iff_source_exists (l : PrimeGeFive) :
    InitialThetaData.{u} l ↔ SourceNativeInitialThetaExists.{u} l := by
  rfl

theorem quantifier_iff_exists (l : PrimeGeFive) :
    (∃ A : InitialThetaArithmeticData.{u} l,
      ∃ T : SourceInitialThetaTuple (A := A),
      SourceNativeInitialThetaPredicate A T) ↔
    SourceNativeInitialThetaExists.{u} l := by
  rfl

theorem sourceNativeInitialThetaExists_iff_packaged (l : PrimeGeFive) :
    SourceNativeInitialThetaExists.{u} l ↔
      Nonempty (SourceNativeInitialThetaData.{u} l) := by
  constructor
  · rintro ⟨A, T, clauseA, clauseB, clauseC, clauseD, clauseE, clauseF, _⟩
    let packaged : SourceNativeInitialThetaData.{u} l :=
      { arithmetic := A
        tuple := T
        clauseA := clauseA
        clauseB := clauseB
        clauseC := clauseC
        clauseD := clauseD
        clauseE := clauseE
        clauseF := clauseF }
    exact ⟨packaged⟩
  · rintro ⟨T⟩
    exact ⟨T.arithmetic, T.tuple, T.clauseA, T.clauseB, T.clauseC,
      T.clauseD, T.clauseE, T.clauseF, rfl⟩

/-!
  This is the exact arithmetic-to-source construction gate. The equality is
  part of the type so that a witness cannot silently change the arithmetic
  input while supplying an unrelated source tuple. No constructor is claimed
  here: closing this proposition requires construction of every source object
  and every clause from the cited foundations.
-/
def SourceNativeArithmeticToSourceGate (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{u} l,
      ∃ T : SourceNativeInitialThetaData.{u} l,
      T.arithmetic = A

theorem sourceNativeArithmeticToSourceGate_spec
    (l : PrimeGeFive)
    (h : SourceNativeArithmeticToSourceGate.{u} l)
    (A : InitialThetaArithmeticData.{u} l) :
    ∃ T : SourceNativeInitialThetaData.{u} l,
      T.arithmetic = A :=
  h A

end InitialThetaSource

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def initialThetaQuantifierBoundary : Obligation :=
  { id := "IUT-I.definition-3.1-A2-quantifier-boundary"
    source := "IUT I, Definition 3.1(a)-(f), pp. 61-64"
    status := VerificationStatus.interface
    note :=
      "The six dependent clauses quantify over actual fields, punctured " ++
        "elliptic curves, selected number-field places, represented " ++
        "hyperbolic orbicurves, finite-etale covers, profinite exact sequences, " ++
        "Tate curve comparisons, and boundary cusps. The file proves only the " ++
        "dependent-tuple assembly and its existential reformulation; it does " ++
        "not assert existence of source data from arbitrary arithmetic input."
    dependsOn :=
      [ "IUT-I.initial-theta-arithmetic-data",
        "Foundations.NumberField.places",
        "Foundations.Geometry.tate-point-quotient-boundary",
        "IUT-I.initial-theta-data" ] }

def initialThetaArithmeticToSourceGate : Obligation :=
  { id := "IUT-I.definition-3.1-A2-arithmetic-to-source-gate"
    source := "Project extension; source construction for IUT I, Definition 3.1"
    status := VerificationStatus.pending
    note :=
      "SourceNativeArithmeticToSourceGate is the explicit universal gate " ++
        "from InitialThetaArithmeticData to a complete source datum. It is " ++
        "not a premise of the paper's fixed-input quantifier and has no " ++
        "constructor here. Closing it requires source-faithful construction " ++
        "of the six-tuple and clauses (a)-(f), including local groups and the " ++
        "cusp origin."
    dependsOn := [ "IUT-I.definition-3.1-A2-quantifier-boundary" ] }

end LeanFormal.IUT.Audit
