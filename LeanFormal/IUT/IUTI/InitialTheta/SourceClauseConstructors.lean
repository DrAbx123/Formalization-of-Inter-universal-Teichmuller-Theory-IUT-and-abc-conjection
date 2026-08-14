/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

/-!
  # Canonical constructors for the source clauses

  The records in `SourceDefinition31Quantifiers` are the literal source
  contract.  This file does not weaken that contract and does not manufacture
  any of its missing mathematical hypotheses.  It supplies the constructions
  that are already forced by the source objects:

  * the exact sequence attached to an actual orbicurve fundamental-group
    datum is reused by `SourceOrbicurveGroupData`;
  * a Tate comparison is packaged together with its own q-order proof;
  * Clause (c)'s representation is fixed to the actual Galois representation
    of the supplied torsion basis;
  * Clause (e)'s selected-place fields are projected from the same restriction
    section as the sign-quotient datum;
  * Clause (f)'s rank-one quotient is constructed from the actual K-side basis
    from Clause (c), while the source cusp-origin map remains an explicit
    dependency.

  The constructors therefore have source-facing hypotheses exactly where the
  paper has source-facing hypotheses.  In particular, no constructor below
  has type `InitialThetaArithmeticData -> SourceClause...` without the
  corresponding original reduction, Galois, orbicurve, local, or boundary
  witness.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

namespace InitialThetaSource

open CategoryTheory

/-! ## Fundamental-group and finite-etale bindings -/

namespace SourceOrbicurveGroupData

variable {F : Type u} [Field F]
variable {X : Iut.HyperbolicOrbicurve F}
variable {G : ProfiniteGrp.{u}}

/-!
  The geometric group in a source exact sequence is the closed kernel of the
  actual projection.  This constructor accepts the certified etale
  fundamental group of the represented orbicurve and its actual projection;
  the geometric group cannot be supplied as an unrelated carrier.
-/
noncomputable def ofFundamentalGroup
    (arithmeticGroup : ProfiniteGrp.{u})
    (arithmetic : Iut.OrbicurveEtaleFundamentalGroup X arithmeticGroup)
    (projection : arithmeticGroup ⟶ G)
    (projection_surjective : Function.Surjective projection)
    (geometric : Iut.OrbicurveEtaleFundamentalGroup X
      (Iut.closedSubgroupProfiniteGrp
        (Iut.profiniteKernelClosedSubgroup projection))) :
    SourceOrbicurveGroupData X G where
  groups :=
    { arithmeticGroup := arithmeticGroup
      arithmetic := arithmetic
      projection := projection
      projection_surjective := projection_surjective
      geometric := geometric }

@[simp] theorem ofFundamentalGroup_groups
    (arithmeticGroup : ProfiniteGrp.{u})
    (arithmetic : Iut.OrbicurveEtaleFundamentalGroup X arithmeticGroup)
    (projection : arithmeticGroup ⟶ G)
    (projection_surjective : Function.Surjective projection)
    (geometric : Iut.OrbicurveEtaleFundamentalGroup X
      (Iut.closedSubgroupProfiniteGrp
        (Iut.profiniteKernelClosedSubgroup projection))) :
    (ofFundamentalGroup arithmeticGroup arithmetic projection
      projection_surjective geometric).groups =
      { arithmeticGroup := arithmeticGroup
        arithmetic := arithmetic
        projection := projection
        projection_surjective := projection_surjective
        geometric := geometric } :=
  rfl

@[simp] theorem ofFundamentalGroup_arithmeticGroup
    (arithmeticGroup : ProfiniteGrp.{u})
    (arithmetic : Iut.OrbicurveEtaleFundamentalGroup X arithmeticGroup)
    (projection : arithmeticGroup ⟶ G)
    (projection_surjective : Function.Surjective projection)
    (geometric : Iut.OrbicurveEtaleFundamentalGroup X
      (Iut.closedSubgroupProfiniteGrp
        (Iut.profiniteKernelClosedSubgroup projection))) :
    (ofFundamentalGroup arithmeticGroup arithmetic projection
      projection_surjective geometric).groups.arithmeticGroup =
      arithmeticGroup :=
  rfl

@[simp] theorem ofFundamentalGroup_projection
    (arithmeticGroup : ProfiniteGrp.{u})
    (arithmetic : Iut.OrbicurveEtaleFundamentalGroup X arithmeticGroup)
    (projection : arithmeticGroup ⟶ G)
    (projection_surjective : Function.Surjective projection)
    (geometric : Iut.OrbicurveEtaleFundamentalGroup X
      (Iut.closedSubgroupProfiniteGrp
        (Iut.profiniteKernelClosedSubgroup projection))) :
    (ofFundamentalGroup arithmeticGroup arithmetic projection
      projection_surjective geometric).groups.projection = projection :=
  rfl

theorem ofFundamentalGroup_projection_surjective
    (arithmeticGroup : ProfiniteGrp.{u})
    (arithmetic : Iut.OrbicurveEtaleFundamentalGroup X arithmeticGroup)
    (projection : arithmeticGroup ⟶ G)
    (projection_surjective : Function.Surjective projection)
    (geometric : Iut.OrbicurveEtaleFundamentalGroup X
      (Iut.closedSubgroupProfiniteGrp
        (Iut.profiniteKernelClosedSubgroup projection))) :
    Function.Surjective
      (ofFundamentalGroup arithmeticGroup arithmetic projection
        projection_surjective geometric).groups.projection :=
  projection_surjective

noncomputable def exactSequenceOfFundamentalGroup
    (arithmeticGroup : ProfiniteGrp.{u})
    (arithmetic : Iut.OrbicurveEtaleFundamentalGroup X arithmeticGroup)
    (projection : arithmeticGroup ⟶ G)
    (projection_surjective : Function.Surjective projection)
    (geometric : Iut.OrbicurveEtaleFundamentalGroup X
      (Iut.closedSubgroupProfiniteGrp
        (Iut.profiniteKernelClosedSubgroup projection))) :=
  Iut.OrbicurveFundamentalGroupData.exactSequence
    (ofFundamentalGroup arithmeticGroup arithmetic projection
      projection_surjective geometric).groups

theorem exactSequenceOfFundamentalGroup_projection
    (arithmeticGroup : ProfiniteGrp.{u})
    (arithmetic : Iut.OrbicurveEtaleFundamentalGroup X arithmeticGroup)
    (projection : arithmeticGroup ⟶ G)
    (projection_surjective : Function.Surjective projection)
    (geometric : Iut.OrbicurveEtaleFundamentalGroup X
      (Iut.closedSubgroupProfiniteGrp
        (Iut.profiniteKernelClosedSubgroup projection))) :
    (exactSequenceOfFundamentalGroup arithmeticGroup arithmetic projection
      projection_surjective geometric).projection = projection :=
  rfl

theorem exactSequenceOfFundamentalGroup_inclusion_injective
    (arithmeticGroup : ProfiniteGrp.{u})
    (arithmetic : Iut.OrbicurveEtaleFundamentalGroup X arithmeticGroup)
    (projection : arithmeticGroup ⟶ G)
    (projection_surjective : Function.Surjective projection)
    (geometric : Iut.OrbicurveEtaleFundamentalGroup X
      (Iut.closedSubgroupProfiniteGrp
        (Iut.profiniteKernelClosedSubgroup projection))) :
    Function.Injective
      (exactSequenceOfFundamentalGroup arithmeticGroup arithmetic projection
        projection_surjective geometric).inclusion :=
  Iut.ProfiniteFundamentalExactSequence.inclusion_injective
    (exactSequenceOfFundamentalGroup arithmeticGroup arithmetic projection
      projection_surjective geometric)

theorem exactSequenceOfFundamentalGroup_projection_surjective
    (arithmeticGroup : ProfiniteGrp.{u})
    (arithmetic : Iut.OrbicurveEtaleFundamentalGroup X arithmeticGroup)
    (projection : arithmeticGroup ⟶ G)
    (projection_surjective : Function.Surjective projection)
    (geometric : Iut.OrbicurveEtaleFundamentalGroup X
      (Iut.closedSubgroupProfiniteGrp
        (Iut.profiniteKernelClosedSubgroup projection))) :
    Function.Surjective
      (exactSequenceOfFundamentalGroup arithmeticGroup arithmetic projection
        projection_surjective geometric).projection :=
  Iut.ProfiniteFundamentalExactSequence.projection_surjective
    (exactSequenceOfFundamentalGroup arithmeticGroup arithmetic projection
      projection_surjective geometric)

end SourceOrbicurveGroupData

namespace SourceOrbicurveFiniteEtaleCover

variable {F : Type u} [Field F]
variable {source target : Iut.HyperbolicOrbicurve F}

/-! Bind a map and its actual representable finite-etale certificate. -/
def ofMap
    (map : source.Hom target)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map) :
    SourceOrbicurveFiniteEtaleCover source target where
  map := map
  finiteEtale := finiteEtale

@[simp] theorem ofMap_map
    (map : source.Hom target)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map) :
    (ofMap map finiteEtale).map = map :=
  rfl

@[simp] theorem ofMap_finiteEtale
    (map : source.Hom target)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map) :
    (ofMap map finiteEtale).finiteEtale = finiteEtale :=
  rfl

def ofMap_map_is_finite_etale
    (map : source.Hom target)
    (finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map) :
    Iut.EtaleStackFiniteEtaleMorphism (ofMap map finiteEtale).map :=
  (ofMap map finiteEtale).finiteEtale

end SourceOrbicurveFiniteEtaleCover

/-! ## Clause (a): reduction-case binding -/

namespace SourceClauseA

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}

/-!
  A source proof of good-or-multiplicative reduction is converted to the
  literal stable-reduction predicate by the two proved foundation lemmas.
  The field-of-moduli and maximal-solvable witnesses remain explicit because
  neither follows from `InitialThetaArithmeticData`.
-/
noncomputable def ofGoodOrMultiplicativeReduction
    (reductionCases : ∀ p : NumberField.FinitePlace A.F,
      A.curve.HasGoodReductionAt p ∨ A.curve.HasMultiplicativeReductionAt p)
    (fieldOfModuli : SourceFieldOfModuli A)
    (maximalSolvableExtension : IntermediateField A.Fmod A.F)
    (maximalSolvableProperty :
      isFiniteSolvableGaloisSubextension maximalSolvableExtension)
    (maximalSolvableContains :
      ∀ E : IntermediateField A.Fmod A.F,
        isFiniteSolvableGaloisSubextension E →
          E ≤ maximalSolvableExtension) :
    SourceClauseA A S where
  stable_reduction_nonarchimedean := by
    intro p
    rcases reductionCases p with hgood | hmult
    · exact PuncturedEllipticCurve.hasGoodReductionAt_imp_stable hgood
    · exact PuncturedEllipticCurve.hasMultiplicativeReductionAt_imp_stable hmult
  field_of_moduli := fieldOfModuli
  maximal_solvable_extension := maximalSolvableExtension
  maximal_solvable_property := maximalSolvableProperty
  maximal_solvable_contains := maximalSolvableContains

theorem ofGoodOrMultiplicativeReduction_stable
    (reductionCases : ∀ p : NumberField.FinitePlace A.F,
      A.curve.HasGoodReductionAt p ∨ A.curve.HasMultiplicativeReductionAt p)
    (p : NumberField.FinitePlace A.F) :
    A.curve.HasStableReductionAt p := by
  rcases reductionCases p with hgood | hmult
  · exact PuncturedEllipticCurve.hasGoodReductionAt_imp_stable hgood
  · exact PuncturedEllipticCurve.hasMultiplicativeReductionAt_imp_stable hmult

@[simp] theorem ofGoodOrMultiplicativeReduction_field_of_moduli
    (reductionCases : ∀ p : NumberField.FinitePlace A.F,
      A.curve.HasGoodReductionAt p ∨ A.curve.HasMultiplicativeReductionAt p)
    (fieldOfModuli : SourceFieldOfModuli A)
    (maximalSolvableExtension : IntermediateField A.Fmod A.F)
    (maximalSolvableProperty :
      isFiniteSolvableGaloisSubextension maximalSolvableExtension)
    (maximalSolvableContains :
      ∀ E : IntermediateField A.Fmod A.F,
        isFiniteSolvableGaloisSubextension E →
          E ≤ maximalSolvableExtension) :
    (ofGoodOrMultiplicativeReduction (S := S) reductionCases fieldOfModuli
      maximalSolvableExtension maximalSolvableProperty
      maximalSolvableContains).field_of_moduli = fieldOfModuli :=
  rfl

@[simp] theorem ofGoodOrMultiplicativeReduction_maximal_extension
    (reductionCases : ∀ p : NumberField.FinitePlace A.F,
      A.curve.HasGoodReductionAt p ∨ A.curve.HasMultiplicativeReductionAt p)
    (fieldOfModuli : SourceFieldOfModuli A)
    (maximalSolvableExtension : IntermediateField A.Fmod A.F)
    (maximalSolvableProperty :
      isFiniteSolvableGaloisSubextension maximalSolvableExtension)
    (maximalSolvableContains :
      ∀ E : IntermediateField A.Fmod A.F,
        isFiniteSolvableGaloisSubextension E →
          E ≤ maximalSolvableExtension) :
    (ofGoodOrMultiplicativeReduction (S := S) reductionCases fieldOfModuli
      maximalSolvableExtension maximalSolvableProperty
      maximalSolvableContains).maximal_solvable_extension =
      maximalSolvableExtension :=
  rfl

theorem ofGoodOrMultiplicativeReduction_maximal_property
    (reductionCases : ∀ p : NumberField.FinitePlace A.F,
      A.curve.HasGoodReductionAt p ∨ A.curve.HasMultiplicativeReductionAt p)
    (fieldOfModuli : SourceFieldOfModuli A)
    (maximalSolvableExtension : IntermediateField A.Fmod A.F)
    (maximalSolvableProperty :
      isFiniteSolvableGaloisSubextension maximalSolvableExtension)
    (maximalSolvableContains :
      ∀ E : IntermediateField A.Fmod A.F,
        isFiniteSolvableGaloisSubextension E →
          E ≤ maximalSolvableExtension) :
    isFiniteSolvableGaloisSubextension
      (ofGoodOrMultiplicativeReduction (S := S) reductionCases fieldOfModuli
        maximalSolvableExtension maximalSolvableProperty
        maximalSolvableContains).maximal_solvable_extension :=
  maximalSolvableProperty

theorem ofGoodOrMultiplicativeReduction_maximality
    (reductionCases : ∀ p : NumberField.FinitePlace A.F,
      A.curve.HasGoodReductionAt p ∨ A.curve.HasMultiplicativeReductionAt p)
    (fieldOfModuli : SourceFieldOfModuli A)
    (maximalSolvableExtension : IntermediateField A.Fmod A.F)
    (maximalSolvableProperty :
      isFiniteSolvableGaloisSubextension maximalSolvableExtension)
    (maximalSolvableContains :
      ∀ E : IntermediateField A.Fmod A.F,
        isFiniteSolvableGaloisSubextension E →
          E ≤ maximalSolvableExtension)
    (E : IntermediateField A.Fmod A.F)
    (hE : isFiniteSolvableGaloisSubextension E) :
    E ≤
      (ofGoodOrMultiplicativeReduction (S := S) reductionCases fieldOfModuli
        maximalSolvableExtension maximalSolvableProperty
        maximalSolvableContains).maximal_solvable_extension :=
  maximalSolvableContains E hE

end SourceClauseA

/-! ## Clause (b): Tate comparison binding -/

namespace SourceTateComparisonWitness

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {p : NumberField.FinitePlace A.F}

/-! The q-parameter and Tate comparison are retained as one dependent witness. -/
def ofComparison
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate p)
    (comparison : TateCurveComparison A.curve p parameter)
    (orderCoprime : Nat.Coprime parameter.order l.value) :
    SourceTateComparisonWitness A p where
  parameter := parameter
  comparison := comparison
  order_coprime := orderCoprime

@[simp] theorem ofComparison_parameter
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate p)
    (comparison : TateCurveComparison A.curve p parameter)
    (orderCoprime : Nat.Coprime parameter.order l.value) :
    (ofComparison parameter comparison orderCoprime).parameter = parameter :=
  rfl

@[simp] theorem ofComparison_comparison
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate p)
    (comparison : TateCurveComparison A.curve p parameter)
    (orderCoprime : Nat.Coprime parameter.order l.value) :
    (ofComparison parameter comparison orderCoprime).comparison = comparison :=
  rfl

theorem ofComparison_order_coprime
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate p)
    (comparison : TateCurveComparison A.curve p parameter)
    (orderCoprime : Nat.Coprime parameter.order l.value) :
    Nat.Coprime (ofComparison parameter comparison orderCoprime).parameter.order
      l.value :=
  orderCoprime

end SourceTateComparisonWitness

namespace SourceClauseB

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}

/-!
  The source comparison quantifier is written in its witness form.  The
  constructor packages each supplied parameter, comparison, and independent
  q-order coprimality proof into the exact `SourceTateComparisonWitness`.
-/
theorem ofTateComparisonWitnesses
    (multiplicative : ∀ (p : NumberField.FinitePlace A.F),
      NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad →
      A.curve.HasMultiplicativeReductionAt p)
    (qWitness : ∀ (p : NumberField.FinitePlace A.F),
      (hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad) →
      Nonempty (SourceTateComparisonWitness A p))
    (residueCharacteristicCoprime : ∀ (p : NumberField.FinitePlace A.F),
      NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad →
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := A.Fmod) p))) :
    SourceClauseB A S C where
  multiplicative_over_bad := multiplicative
  q_comparison := qWitness
  residue_characteristic_prime_to_l := residueCharacteristicCoprime

theorem ofTateComparisonWitnesses_multiplicative
    (multiplicative : ∀ (p : NumberField.FinitePlace A.F),
      NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad →
      A.curve.HasMultiplicativeReductionAt p)
    (p : NumberField.FinitePlace A.F)
    (hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad) :
    A.curve.HasMultiplicativeReductionAt p :=
  multiplicative p hp

theorem ofTateComparisonWitnesses_q_comparison
    (qWitness : ∀ (p : NumberField.FinitePlace A.F),
      (hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad) →
      Nonempty (SourceTateComparisonWitness A p))
    (p : NumberField.FinitePlace A.F)
    (hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad) :
    Nonempty (SourceTateComparisonWitness A p) :=
  qWitness p hp

theorem ofTateComparisonWitnesses_residue_coprime
    (residueCharacteristicCoprime : ∀ (p : NumberField.FinitePlace A.F),
      NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad →
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := A.Fmod) p)))
    (p : NumberField.FinitePlace A.F)
    (hp : NumberFieldFinitePlace.comap (k := A.Fmod) p ∈ S.V_mod_bad) :
    Nat.Coprime l.value
      (NumberFieldFinitePlace.residueCharacteristic
        (NumberFieldFinitePlace.comap (k := A.Fmod) p)) :=
  residueCharacteristicCoprime p hp

end SourceClauseB

/-! ## Clause (c): canonical Galois representation binding -/

namespace SourceClauseC

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}

/-!
  The representation is not an independently selected monoid homomorphism.
  Once the actual F-side torsion basis is supplied, it is definitionally the
  representation from `EllipticTorsion.lean`; only the source large-image and
  kernel-field identification statements remain hypotheses.
-/
noncomputable def ofCanonicalRepresentation
    (torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve)
    (torsionBasis :
      (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l)
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
        (A.curve.galoisLTorsionMatrixRepresentation l torsionBasis).range)
    (kernelFieldIdentification :
      A.K ≃ₐ[A.F]
        A.curve.galoisLTorsionKernelField l torsionBasis)
    (kernelFieldIdentificationRange :
      Set.range (fun x : A.K =>
        (kernelFieldIdentification x : AlgebraicClosure A.F)) =
      (A.curve.galoisLTorsionKernelField l torsionBasis :
        Set (AlgebraicClosure A.F))) :
    SourceClauseC A S C B where
  torsion23_rational := torsion23Rational
  torsion_basis := torsionBasis
  representation := A.curve.galoisLTorsionMatrixRepresentation l torsionBasis
  representation_eq_canonical := rfl
  image_contains_SL2 := imageContainsSL2
  kernel_field_identification := kernelFieldIdentification
  kernel_field_identification_range := kernelFieldIdentificationRange

@[simp] theorem ofCanonicalRepresentation_torsion_basis
    (torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve)
    (torsionBasis :
      (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l)
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
        (A.curve.galoisLTorsionMatrixRepresentation l torsionBasis).range)
    (kernelFieldIdentification :
      A.K ≃ₐ[A.F]
        A.curve.galoisLTorsionKernelField l torsionBasis)
    (kernelFieldIdentificationRange :
      Set.range (fun x : A.K =>
        (kernelFieldIdentification x : AlgebraicClosure A.F)) =
      (A.curve.galoisLTorsionKernelField l torsionBasis :
        Set (AlgebraicClosure A.F))) :
    (ofCanonicalRepresentation (S := S) (C := C) (B := B)
      torsion23Rational torsionBasis imageContainsSL2
      kernelFieldIdentification kernelFieldIdentificationRange).torsion_basis =
      torsionBasis :=
  rfl

@[simp] theorem ofCanonicalRepresentation_representation
    (torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve)
    (torsionBasis :
      (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l)
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
        (A.curve.galoisLTorsionMatrixRepresentation l torsionBasis).range)
    (kernelFieldIdentification :
      A.K ≃ₐ[A.F]
        A.curve.galoisLTorsionKernelField l torsionBasis)
    (kernelFieldIdentificationRange :
      Set.range (fun x : A.K =>
        (kernelFieldIdentification x : AlgebraicClosure A.F)) =
      (A.curve.galoisLTorsionKernelField l torsionBasis :
        Set (AlgebraicClosure A.F))) :
    (ofCanonicalRepresentation (S := S) (C := C) (B := B)
      torsion23Rational torsionBasis imageContainsSL2
      kernelFieldIdentification kernelFieldIdentificationRange).representation =
      A.curve.galoisLTorsionMatrixRepresentation l torsionBasis :=
  rfl

theorem ofCanonicalRepresentation_representation_continuous
    (torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve)
    (torsionBasis :
      (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l)
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
        (A.curve.galoisLTorsionMatrixRepresentation l torsionBasis).range)
    (kernelFieldIdentification :
      A.K ≃ₐ[A.F]
        A.curve.galoisLTorsionKernelField l torsionBasis)
    (kernelFieldIdentificationRange :
      Set.range (fun x : A.K =>
        (kernelFieldIdentification x : AlgebraicClosure A.F)) =
      (A.curve.galoisLTorsionKernelField l torsionBasis :
        Set (AlgebraicClosure A.F))) :
    Continuous
      (ofCanonicalRepresentation (S := S) (C := C) (B := B)
        torsion23Rational torsionBasis
        imageContainsSL2 kernelFieldIdentification
        kernelFieldIdentificationRange).representation := by
  rw [ofCanonicalRepresentation_representation]
  exact A.curve.galoisLTorsionMatrixRepresentation_continuous l torsionBasis

theorem ofCanonicalRepresentation_image_spec
    (torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve)
    (torsionBasis :
      (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l)
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
        (A.curve.galoisLTorsionMatrixRepresentation l torsionBasis).range)
    (kernelFieldIdentification :
      A.K ≃ₐ[A.F]
        A.curve.galoisLTorsionKernelField l torsionBasis)
    (kernelFieldIdentificationRange :
      Set.range (fun x : A.K =>
        (kernelFieldIdentification x : AlgebraicClosure A.F)) =
      (A.curve.galoisLTorsionKernelField l torsionBasis :
        Set (AlgebraicClosure A.F))) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (ofCanonicalRepresentation (S := S) (C := C) (B := B)
        torsion23Rational torsionBasis
        imageContainsSL2 kernelFieldIdentification
        kernelFieldIdentificationRange).representation.range :=
  imageContainsSL2

theorem ofCanonicalRepresentation_kernel_field_range
    (_torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve)
    (torsionBasis :
      (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l)
    (_imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
        (A.curve.galoisLTorsionMatrixRepresentation l torsionBasis).range)
    (kernelFieldIdentification :
      A.K ≃ₐ[A.F]
        A.curve.galoisLTorsionKernelField l torsionBasis)
    (kernelFieldIdentificationRange :
      Set.range (fun x : A.K =>
        (kernelFieldIdentification x : AlgebraicClosure A.F)) =
      (A.curve.galoisLTorsionKernelField l torsionBasis :
        Set (AlgebraicClosure A.F))) :
    Set.range (fun x : A.K =>
      (kernelFieldIdentification x : AlgebraicClosure A.F)) =
      (A.curve.galoisLTorsionKernelField l torsionBasis :
        Set (AlgebraicClosure A.F)) :=
  kernelFieldIdentificationRange

end SourceClauseC

/-! ## Clause (d): dependent quotient and cover bindings -/

namespace SourceClauseD

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}
variable {D : SourceClauseC A S C B}

/-!
  The constructor exposes all K-side source witnesses in one place.  The
  quotient-extension equality and the finite-etale equality are retained as
  dependent equalities, so the cover cannot be silently replaced by another
  map with the same carrier types.
-/
noncomputable def ofKSideWitnesses
    (kSignAction : Iut.OrbicurveSignAction S.xK)
    (kQuotient : Iut.OrbicurveSignInvariantMorphism kSignAction S.cK)
    (kQuotientWitness :
      Iut.OrbicurveSignQuotientWitness kSignAction kQuotient)
    (kQuotientExtension : SourceOrbicurveMorphismScalarExtension
      S.xKExtension S.cKExtension S.quotient.map)
    (kQuotientMapEqExtension :
      kQuotient.map = Iut.HyperbolicOrbicurve.Hom.cast
        S.xK_eq_extension.symm S.cK_eq_extension.symm
        kQuotientExtension.result)
    (kTorsionCover : SourceOrbicurveFiniteEtaleCover S.xK S.cK)
    (kTorsionCoverMapEqQuotient :
      kTorsionCover.map = kQuotient.map)
    (xGroups : SourceOrbicurveGroupData S.xK
      (Iut.AbsoluteGaloisProfinite A.K))
    (cGroups : SourceOrbicurveGroupData S.cK
      (Iut.AbsoluteGaloisProfinite A.K))
    (groupInclusion :
      Iut.ProfiniteFundamentalGroupInclusion
        xGroups.sequence.geometric xGroups.sequence.arithmetic
        cGroups.sequence.geometric cGroups.sequence.arithmetic
        (Iut.AbsoluteGaloisProfinite A.K)
        xGroups.sequence cGroups.sequence)
    (xToFGroups :
      Iut.ProfiniteFundamentalExactSequenceEmbedding
        xGroups.sequence.geometric xGroups.sequence.arithmetic
        (Iut.AbsoluteGaloisProfinite A.K)
        S.xFGroups.sequence.geometric S.xFGroups.sequence.arithmetic
        (Iut.AbsoluteGaloisProfinite A.F)
        xGroups.sequence S.xFGroups.sequence)
    (cToFGroups :
      Iut.ProfiniteFundamentalExactSequenceEmbedding
        cGroups.sequence.geometric cGroups.sequence.arithmetic
        (Iut.AbsoluteGaloisProfinite A.K)
        S.cFGroups.sequence.geometric S.cFGroups.sequence.arithmetic
        (Iut.AbsoluteGaloisProfinite A.F)
        cGroups.sequence S.cFGroups.sequence) :
    SourceClauseD A S C B D where
  k_signAction := kSignAction
  k_quotient := kQuotient
  k_quotientWitness := kQuotientWitness
  k_quotientExtension := kQuotientExtension
  k_quotient_map_eq_extension := kQuotientMapEqExtension
  k_l_torsion_cover := kTorsionCover
  k_l_torsion_cover_map_eq_quotient := kTorsionCoverMapEqQuotient
  x_groups := xGroups
  c_groups := cGroups
  group_inclusion := groupInclusion
  x_to_F_groups := xToFGroups
  c_to_F_groups := cToFGroups

@[simp] theorem ofKSideWitnesses_signAction
    (kSignAction : Iut.OrbicurveSignAction S.xK)
    (kQuotient : Iut.OrbicurveSignInvariantMorphism kSignAction S.cK)
    (kQuotientWitness :
      Iut.OrbicurveSignQuotientWitness kSignAction kQuotient)
    (kQuotientExtension : SourceOrbicurveMorphismScalarExtension
      S.xKExtension S.cKExtension S.quotient.map)
    (kQuotientMapEqExtension :
      kQuotient.map = Iut.HyperbolicOrbicurve.Hom.cast
        S.xK_eq_extension.symm S.cK_eq_extension.symm
        kQuotientExtension.result)
    (kTorsionCover : SourceOrbicurveFiniteEtaleCover S.xK S.cK)
    (kTorsionCoverMapEqQuotient : kTorsionCover.map = kQuotient.map)
    (xGroups : SourceOrbicurveGroupData S.xK
      (Iut.AbsoluteGaloisProfinite A.K))
    (cGroups : SourceOrbicurveGroupData S.cK
      (Iut.AbsoluteGaloisProfinite A.K))
    (groupInclusion : Iut.ProfiniteFundamentalGroupInclusion
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K) xGroups.sequence cGroups.sequence)
    (xToFGroups : Iut.ProfiniteFundamentalExactSequenceEmbedding
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      S.xFGroups.sequence.geometric S.xFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.F) xGroups.sequence S.xFGroups.sequence)
    (cToFGroups : Iut.ProfiniteFundamentalExactSequenceEmbedding
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      S.cFGroups.sequence.geometric S.cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.F) cGroups.sequence S.cFGroups.sequence) :
    (ofKSideWitnesses (S := S) (C := C) (B := B) (D := D)
      kSignAction kQuotient kQuotientWitness
      kQuotientExtension kQuotientMapEqExtension kTorsionCover
      kTorsionCoverMapEqQuotient xGroups cGroups groupInclusion xToFGroups
      cToFGroups).k_signAction = kSignAction :=
  rfl

@[simp] theorem ofKSideWitnesses_quotient
    (kSignAction : Iut.OrbicurveSignAction S.xK)
    (kQuotient : Iut.OrbicurveSignInvariantMorphism kSignAction S.cK)
    (kQuotientWitness :
      Iut.OrbicurveSignQuotientWitness kSignAction kQuotient)
    (kQuotientExtension : SourceOrbicurveMorphismScalarExtension
      S.xKExtension S.cKExtension S.quotient.map)
    (kQuotientMapEqExtension :
      kQuotient.map = Iut.HyperbolicOrbicurve.Hom.cast
        S.xK_eq_extension.symm S.cK_eq_extension.symm
        kQuotientExtension.result)
    (kTorsionCover : SourceOrbicurveFiniteEtaleCover S.xK S.cK)
    (kTorsionCoverMapEqQuotient : kTorsionCover.map = kQuotient.map)
    (xGroups : SourceOrbicurveGroupData S.xK
      (Iut.AbsoluteGaloisProfinite A.K))
    (cGroups : SourceOrbicurveGroupData S.cK
      (Iut.AbsoluteGaloisProfinite A.K))
    (groupInclusion : Iut.ProfiniteFundamentalGroupInclusion
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K) xGroups.sequence cGroups.sequence)
    (xToFGroups : Iut.ProfiniteFundamentalExactSequenceEmbedding
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      S.xFGroups.sequence.geometric S.xFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.F) xGroups.sequence S.xFGroups.sequence)
    (cToFGroups : Iut.ProfiniteFundamentalExactSequenceEmbedding
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      S.cFGroups.sequence.geometric S.cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.F) cGroups.sequence S.cFGroups.sequence) :
    (ofKSideWitnesses (S := S) (C := C) (B := B) (D := D)
      kSignAction kQuotient kQuotientWitness
      kQuotientExtension kQuotientMapEqExtension kTorsionCover
      kTorsionCoverMapEqQuotient xGroups cGroups groupInclusion xToFGroups
      cToFGroups).k_quotient = kQuotient :=
  rfl

theorem ofKSideWitnesses_group_projections
    (kSignAction : Iut.OrbicurveSignAction S.xK)
    (kQuotient : Iut.OrbicurveSignInvariantMorphism kSignAction S.cK)
    (kQuotientWitness :
      Iut.OrbicurveSignQuotientWitness kSignAction kQuotient)
    (kQuotientExtension : SourceOrbicurveMorphismScalarExtension
      S.xKExtension S.cKExtension S.quotient.map)
    (kQuotientMapEqExtension :
      kQuotient.map = Iut.HyperbolicOrbicurve.Hom.cast
        S.xK_eq_extension.symm S.cK_eq_extension.symm
        kQuotientExtension.result)
    (kTorsionCover : SourceOrbicurveFiniteEtaleCover S.xK S.cK)
    (kTorsionCoverMapEqQuotient : kTorsionCover.map = kQuotient.map)
    (xGroups : SourceOrbicurveGroupData S.xK
      (Iut.AbsoluteGaloisProfinite A.K))
    (cGroups : SourceOrbicurveGroupData S.cK
      (Iut.AbsoluteGaloisProfinite A.K))
    (groupInclusion : Iut.ProfiniteFundamentalGroupInclusion
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K) xGroups.sequence cGroups.sequence)
    (xToFGroups : Iut.ProfiniteFundamentalExactSequenceEmbedding
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      S.xFGroups.sequence.geometric S.xFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.F) xGroups.sequence S.xFGroups.sequence)
    (cToFGroups : Iut.ProfiniteFundamentalExactSequenceEmbedding
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      S.cFGroups.sequence.geometric S.cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.F) cGroups.sequence S.cFGroups.sequence) :
    (ofKSideWitnesses (S := S) (C := C) (B := B) (D := D)
      kSignAction kQuotient kQuotientWitness
      kQuotientExtension kQuotientMapEqExtension kTorsionCover
      kTorsionCoverMapEqQuotient xGroups cGroups groupInclusion xToFGroups
      cToFGroups).x_groups = xGroups ∧
      (ofKSideWitnesses (S := S) (C := C) (B := B) (D := D)
        kSignAction kQuotient kQuotientWitness
        kQuotientExtension kQuotientMapEqExtension kTorsionCover
        kTorsionCoverMapEqQuotient xGroups cGroups groupInclusion xToFGroups
        cToFGroups).c_groups = cGroups :=
  ⟨rfl, rfl⟩

end SourceClauseD

/-! ## Clause (e): selected places and local families -/

namespace SourceClauseE

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}
variable {D : SourceClauseC A S C B}
variable {E : SourceClauseD A S C B D}

/-!
  `S.V_eq_section` and `S.V_mod_bijection` are the same source-place data
  already carried by the sign quotient.  Only the independent completion-level
  local families remain arguments of this constructor.
-/
noncomputable def ofLocalFamilies
    (finiteLocal : ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
      (hv : v.1.IsFinite),
      SourceFiniteLocalSource A S C B D E (selectedFinitePlace hv))
    (infiniteLocal : ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
      (hv : v.1.IsInfinite),
      SourceInfiniteLocalSource A S C B D E (selectedInfinitePlace hv)) :
    SourceClauseE A S C B D E where
  selected_eq_V := S.V_eq_section
  selected_equiv := S.V_mod_bijection
  finite_local := finiteLocal
  infinite_local := infiniteLocal

@[simp] theorem ofLocalFamilies_selected_eq_V
    (finiteLocal : ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
      (hv : v.1.IsFinite),
      SourceFiniteLocalSource A S C B D E (selectedFinitePlace hv))
    (infiniteLocal : ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
      (hv : v.1.IsInfinite),
      SourceInfiniteLocalSource A S C B D E (selectedInfinitePlace hv)) :
    (ofLocalFamilies finiteLocal infiniteLocal).selected_eq_V =
      S.V_eq_section :=
  rfl

@[simp] theorem ofLocalFamilies_selected_equiv
    (finiteLocal : ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
      (hv : v.1.IsFinite),
      SourceFiniteLocalSource A S C B D E (selectedFinitePlace hv))
    (infiniteLocal : ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
      (hv : v.1.IsInfinite),
      SourceInfiniteLocalSource A S C B D E (selectedInfinitePlace hv)) :
    (ofLocalFamilies finiteLocal infiniteLocal).selected_equiv =
      S.V_mod_bijection :=
  rfl

/-! The two local family projections retain the actual dependent place. -/
noncomputable def finiteLocalSpec
    (finiteLocal : ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
      (hv : v.1.IsFinite),
      SourceFiniteLocalSource A S C B D E (selectedFinitePlace hv))
    (v : {v : NumberFieldPlace A.K // v ∈ S.V})
    (hv : v.1.IsFinite) :
    SourceFiniteLocalSource A S C B D E (selectedFinitePlace hv) :=
  finiteLocal v hv

noncomputable def infiniteLocalSpec
    (infiniteLocal : ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
      (hv : v.1.IsInfinite),
      SourceInfiniteLocalSource A S C B D E (selectedInfinitePlace hv))
    (v : {v : NumberFieldPlace A.K // v ∈ S.V})
    (hv : v.1.IsInfinite) :
    SourceInfiniteLocalSource A S C B D E (selectedInfinitePlace hv) :=
  infiniteLocal v hv

end SourceClauseE

/-! ## Clause (f): K-side quotient and cusp-origin binding -/

namespace SourceClauseF

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}
variable {D : SourceClauseC A S C B}
variable {E : SourceClauseD A S C B D}
variable {L : SourceClauseE A S C B D E}

/-!
  The quotient is constructed from the K-side basis produced by Clause (c).
  This is the exact `E_K[l]`-side carrier supplied by the arithmetic base
  change.  The origin map is still source mathematics: it cannot be derived
  from the algebraic quotient alone, so it remains an explicit argument.
-/
noncomputable def canonicalKQuotientData
    (C : SourceClauseA A S)
    (B : SourceClauseB A S C)
    (D : SourceClauseC A S C B) :
    TorsionRankOneQuotientData l (A.curve.baseChange A.K) where
  torsion_basis := D.k_torsion_basis

@[simp] theorem canonicalKQuotientData_torsion_basis :
    (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
      (B := B) D).torsion_basis = D.k_torsion_basis :=
  rfl

noncomputable def boundaryOriginFromKBasis
    (C : SourceClauseA A S)
    (B : SourceClauseB A S C)
    (D : SourceClauseC A S C B)
    (originMap :
      {q : (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
        (B := B) D).Quotient // q ≠ 0} →
        Iut.OrbicurveBoundaryCusp S.cK)
    (cusp : Iut.OrbicurveBoundaryCusp S.cK)
    (originMap_distinguished :
      originMap
          ⟨(canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
            (B := B) D).distinguishedClass,
            (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
              (B := B) D).distinguishedClass_nonzero⟩ = cusp) :
    TorsionQuotientBoundaryOrigin l A S.cK where
  rank_one_quotient := canonicalKQuotientData (l := l) (A := A)
    (S := S) (C := C) (B := B) D
  originMap := originMap
  cusp := cusp
  originMap_distinguishedClass := originMap_distinguished

@[simp] theorem boundaryOriginFromKBasis_rank_one_quotient
    (originMap :
      {q : (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
        (B := B) D).Quotient // q ≠ 0} →
        Iut.OrbicurveBoundaryCusp S.cK)
    (cusp : Iut.OrbicurveBoundaryCusp S.cK)
    (originMap_distinguished :
      originMap
          ⟨(canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
            (B := B) D).distinguishedClass,
            (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
              (B := B) D).distinguishedClass_nonzero⟩ = cusp) :
    (boundaryOriginFromKBasis (l := l) (A := A) (S := S) (C := C)
      (B := B) D originMap cusp originMap_distinguished).rank_one_quotient =
      canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
        (B := B) D :=
  rfl

@[simp] theorem boundaryOriginFromKBasis_cusp
    (originMap :
      {q : (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
        (B := B) D).Quotient // q ≠ 0} →
        Iut.OrbicurveBoundaryCusp S.cK)
    (cusp : Iut.OrbicurveBoundaryCusp S.cK)
    (originMap_distinguished :
      originMap
          ⟨(canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
            (B := B) D).distinguishedClass,
            (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
              (B := B) D).distinguishedClass_nonzero⟩ = cusp) :
    (boundaryOriginFromKBasis (l := l) (A := A) (S := S) (C := C)
      (B := B) D originMap cusp originMap_distinguished).cusp = cusp :=
  rfl

/-!
  The cusp in the resulting boundary origin is fixed to `S.epsilon`.  The
  proof of the distinguished origin equation is correspondingly the exact
  source cusp-origin condition, with no independent cusp carrier.
-/
noncomputable def ofCanonicalKBoundaryOrigin
    (C : SourceClauseA A S)
    (B : SourceClauseB A S C)
    (D : SourceClauseC A S C B)
    (originMap :
      {q : (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
        (B := B) D).Quotient // q ≠ 0} →
        Iut.OrbicurveBoundaryCusp S.cK)
    (originMap_epsilon :
      originMap
          ⟨(canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
            (B := B) D).distinguishedClass,
            (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
              (B := B) D).distinguishedClass_nonzero⟩ = S.epsilon) :
    TorsionQuotientBoundaryOrigin l A S.cK :=
  boundaryOriginFromKBasis (l := l) (A := A) (S := S) (C := C)
    (B := B) D originMap S.epsilon originMap_epsilon

@[simp] theorem ofCanonicalKBoundaryOrigin_cusp
    (originMap :
      {q : (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
        (B := B) D).Quotient // q ≠ 0} →
        Iut.OrbicurveBoundaryCusp S.cK)
    (originMap_epsilon :
      originMap
          ⟨(canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
            (B := B) D).distinguishedClass,
            (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
              (B := B) D).distinguishedClass_nonzero⟩ = S.epsilon) :
    (ofCanonicalKBoundaryOrigin (l := l) (A := A) (S := S) (C := C)
      (B := B) D originMap originMap_epsilon).cusp = S.epsilon :=
  rfl

/-! The usable clause constructor takes the origin map and its proved equality. -/
noncomputable def ofCanonicalBoundaryData
    (C : SourceClauseA A S)
    (B : SourceClauseB A S C)
    (D : SourceClauseC A S C B)
    (E : SourceClauseD A S C B D)
    (L : SourceClauseE A S C B D E)
    (originMap :
      {q : (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
        (B := B) D).Quotient // q ≠ 0} →
        Iut.OrbicurveBoundaryCusp S.cK)
    (originMap_epsilon :
      originMap
          ⟨(canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
            (B := B) D).distinguishedClass,
            (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
              (B := B) D).distinguishedClass_nonzero⟩ = S.epsilon)
    (cuspDecomposition :
      Iut.OrbicurveCuspidalDecompositionData E.c_groups.groups)
    (cuspDecomposition_origin :
      cuspDecomposition.cusp =
        (ofCanonicalKBoundaryOrigin (l := l) (A := A) (S := S) (C := C)
          (B := B) D originMap originMap_epsilon).cusp) :
    SourceClauseF A S C B D E L where
  boundary_origin :=
    ofCanonicalKBoundaryOrigin (l := l) (A := A) (S := S) (C := C)
      (B := B) D originMap originMap_epsilon
  quotient_basis_eq_k_torsion_basis := by
    rfl
  boundary_cusp_eq_epsilon := by
    rfl
  cusp_decomposition := cuspDecomposition
  cusp_decomposition_cusp_eq_origin := cuspDecomposition_origin

theorem ofCanonicalBoundaryData_basis_binding
    (originMap :
      {q : (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
        (B := B) D).Quotient // q ≠ 0} →
        Iut.OrbicurveBoundaryCusp S.cK)
    (originMap_epsilon :
      originMap
          ⟨(canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
            (B := B) D).distinguishedClass,
            (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
              (B := B) D).distinguishedClass_nonzero⟩ = S.epsilon)
    (cuspDecomposition :
      Iut.OrbicurveCuspidalDecompositionData E.c_groups.groups)
    (cuspDecomposition_origin :
      cuspDecomposition.cusp =
        (ofCanonicalKBoundaryOrigin (l := l) (A := A) (S := S) (C := C)
          (B := B) D originMap originMap_epsilon).cusp) :
    (ofCanonicalBoundaryData (C := C) (B := B) (D := D)
      (E := E) (L := L)
      originMap originMap_epsilon cuspDecomposition
      cuspDecomposition_origin).boundary_origin.rank_one_quotient.torsion_basis =
      D.k_torsion_basis :=
  rfl

theorem ofCanonicalBoundaryData_cusp_binding
    (originMap :
      {q : (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
        (B := B) D).Quotient // q ≠ 0} →
        Iut.OrbicurveBoundaryCusp S.cK)
    (originMap_epsilon :
      originMap
          ⟨(canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
            (B := B) D).distinguishedClass,
            (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
              (B := B) D).distinguishedClass_nonzero⟩ = S.epsilon)
    (cuspDecomposition :
      Iut.OrbicurveCuspidalDecompositionData E.c_groups.groups)
    (cuspDecomposition_origin :
      cuspDecomposition.cusp =
        (ofCanonicalKBoundaryOrigin (l := l) (A := A) (S := S) (C := C)
          (B := B) D originMap originMap_epsilon).cusp) :
    (ofCanonicalBoundaryData (C := C) (B := B) (D := D)
      (E := E) (L := L)
      originMap originMap_epsilon cuspDecomposition
      cuspDecomposition_origin).boundary_origin.cusp = S.epsilon :=
  rfl

theorem ofCanonicalBoundaryData_origin_map
    (originMap :
      {q : (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
        (B := B) D).Quotient // q ≠ 0} →
        Iut.OrbicurveBoundaryCusp S.cK)
    (originMap_epsilon :
      originMap
          ⟨(canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
            (B := B) D).distinguishedClass,
            (canonicalKQuotientData (l := l) (A := A) (S := S) (C := C)
              (B := B) D).distinguishedClass_nonzero⟩ = S.epsilon)
    (cuspDecomposition :
      Iut.OrbicurveCuspidalDecompositionData E.c_groups.groups)
    (cuspDecomposition_origin :
      cuspDecomposition.cusp =
        (ofCanonicalKBoundaryOrigin (l := l) (A := A) (S := S) (C := C)
          (B := B) D originMap originMap_epsilon).cusp) :
    (ofCanonicalBoundaryData (C := C) (B := B) (D := D)
      (E := E) (L := L)
      originMap originMap_epsilon cuspDecomposition
      cuspDecomposition_origin).boundary_origin.originMap = originMap :=
  rfl

end SourceClauseF

/-! ## A single source-faithful staged package -/

structure SourceClauseConstructionWitness (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData.{u} l
  fbar : SourceFbarExtension arithmetic
  signQuotient : SourceSignQuotientData arithmetic
  clauseA : SourceClauseA arithmetic signQuotient
  clauseB : SourceClauseB arithmetic signQuotient clauseA
  clauseC : SourceClauseC arithmetic signQuotient clauseA clauseB
  clauseD : SourceClauseD arithmetic signQuotient clauseA clauseB clauseC
  clauseE : SourceClauseE arithmetic signQuotient clauseA clauseB clauseC clauseD
  clauseF : SourceClauseF arithmetic signQuotient clauseA clauseB clauseC clauseD
    clauseE

namespace SourceClauseConstructionWitness

variable {l : PrimeGeFive}

/-! The staged package keeps every clause indexed by the same source record. -/
def sourceData
    (W : SourceClauseConstructionWitness.{u} l) :
    SourceNativeInitialThetaData.{u} l where
  arithmetic := W.arithmetic
  tuple :=
    { fbar := W.fbar
      source := W.signQuotient
      xF := W.signQuotient.xF
      xF_eq_source := rfl
      cK := W.signQuotient.cK
      cK_eq_source := rfl
      V := W.signQuotient.V
      V_eq_source := rfl
      V_mod_bad := W.signQuotient.V_mod_bad
      V_mod_bad_eq_source := rfl
      epsilon := W.signQuotient.epsilon
      epsilon_eq_source := rfl }
  clauseA := W.clauseA
  clauseB := W.clauseB
  clauseC := W.clauseC
  clauseD := W.clauseD
  clauseE := W.clauseE
  clauseF := W.clauseF

@[simp] theorem sourceData_arithmetic
    (W : SourceClauseConstructionWitness.{u} l) :
    (W.sourceData).arithmetic = W.arithmetic :=
  rfl

@[simp] theorem sourceData_tuple_source
    (W : SourceClauseConstructionWitness.{u} l) :
    (W.sourceData).tuple.source = W.signQuotient :=
  rfl

@[simp] theorem sourceData_tuple_fbar
    (W : SourceClauseConstructionWitness.{u} l) :
    (W.sourceData).tuple.fbar = W.fbar :=
  rfl

@[simp] theorem sourceData_tuple_xF
    (W : SourceClauseConstructionWitness.{u} l) :
    (W.sourceData).tuple.xF = W.signQuotient.xF :=
  rfl

@[simp] theorem sourceData_tuple_cK
    (W : SourceClauseConstructionWitness.{u} l) :
    (W.sourceData).tuple.cK = W.signQuotient.cK :=
  rfl

@[simp] theorem sourceData_tuple_V
    (W : SourceClauseConstructionWitness.{u} l) :
    (W.sourceData).tuple.V = W.signQuotient.V :=
  rfl

@[simp] theorem sourceData_tuple_V_mod_bad
    (W : SourceClauseConstructionWitness.{u} l) :
    (W.sourceData).tuple.V_mod_bad = W.signQuotient.V_mod_bad :=
  rfl

@[simp] theorem sourceData_tuple_epsilon
    (W : SourceClauseConstructionWitness.{u} l) :
    (W.sourceData).tuple.epsilon = W.signQuotient.epsilon :=
  rfl

theorem sourceData_clauseA
    (W : SourceClauseConstructionWitness.{u} l) :
    W.sourceData.clauseA = W.clauseA :=
  rfl

theorem sourceData_clauseB
    (W : SourceClauseConstructionWitness.{u} l) :
    W.sourceData.clauseB = W.clauseB :=
  rfl

theorem sourceData_clauseC
    (W : SourceClauseConstructionWitness.{u} l) :
    W.sourceData.clauseC = W.clauseC :=
  rfl

theorem sourceData_clauseD
    (W : SourceClauseConstructionWitness.{u} l) :
    W.sourceData.clauseD = W.clauseD :=
  rfl

theorem sourceData_clauseE
    (W : SourceClauseConstructionWitness.{u} l) :
    W.sourceData.clauseE = W.clauseE :=
  rfl

theorem sourceData_clauseF
    (W : SourceClauseConstructionWitness.{u} l) :
    W.sourceData.clauseF = W.clauseF :=
  rfl

end SourceClauseConstructionWitness

end InitialThetaSource

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def initialThetaSourceClauseConstructors : Obligation :=
  { id := "IUT-I.definition-3.1-A2-clause-constructors"
    source := "IUT I, Definition 3.1(a)-(f)"
    status := VerificationStatus.interface
    note :=
      "Canonical bindings now construct the exact sequence from an actual " ++
      "orbicurve fundamental-group projection, package Tate comparisons, fix " ++
      "Clause (c)'s representation to the actual torsion action, project " ++
      "Clause (e)'s selected-place fields from the same section, and build " ++
      "Clause (f)'s rank-one quotient from the K-side torsion basis. The " ++
      "original reduction, kernel-field descent, quotient, local-model, and " ++
      "cusp-origin witnesses remain explicit; no arithmetic universal gate is " ++
      "claimed."
    dependsOn :=
      [ "IUT-I.definition-3.1-A2-quantifier-boundary",
        "IUT-I.initial-theta-place-selection",
        "Foundations.Geometry.elliptic-torsion-galois",
        "Foundations.Geometry.tate-point-quotient-boundary" ] }

end LeanFormal.IUT.Audit
