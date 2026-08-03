/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidBirationalFactor
import Iut.Foundations.SourceModelFrobenioidBirationalAxioms

/-!
# The explicit model as a specialization of generic birationalization

This file identifies the earlier Theorem 5.2 implementation with the generic
construction of Frobenioids I, Proposition 4.4.  The two implementations use
different Hom encodings: the generic target is the categorical localization,
while the model target stores the paper's filtered Hom colimits explicitly.
The correct comparison is therefore categorical rather than definitional.

The localization universal property gives a canonical functor from the
generic target to the filtered-colimit target.  After the tautological
conversion between their two presentations of `F_(Phi^gp)`, the generic raw
divisor functor and the existing model divisor functor are naturally
isomorphic.  Combining this comparison with
`birationalRestrictedFactorIso` recovers the model's existing restricted
factorization from the generic Proposition 4.4(iii) diagram.
-/

open CategoryTheory

namespace Iut.SourceModelFrobenioid.GenericBirationalSpecialization

open SourceModelFrobenioid.Carrier.ColimitBirationalObject

universe u

noncomputable section

variable {D : Type u} [Category.{u} D] [IsConnected D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM}
variable (data : SourceModelFrobenioid.Input Phi)
variable (baseTotallyEpimorphic : ∀ {X Y : D} (arrow : X ⟶ Y), Epi arrow)

/-- The Theorem 5.2 source packaged as the arbitrary presentation consumed by
the generic Proposition 4.4 construction. -/
abbrev sourcePresentation : FrobenioidPresentation :=
  SourceModelFrobenioid.Carrier.frobenioidPresentation
    (Phi := Phi) (data := data) baseTotallyEpimorphic

/-- The explicit filtered-colimit localization inverts the generic
co-angular pre-step denominators. -/
theorem colimitLocalization_inverts :
    (FrobenioidBirationalization.denominators
      (sourcePresentation data baseTotallyEpimorphic)).IsInvertedBy
      (SourceModelFrobenioid.Carrier.ColimitBirationalObject.localizationFunctor
        (Phi := Phi) (data := data)) := by
  intro source target arrow denominator
  exact
    SourceModelFrobenioid.Carrier.ColimitBirationalObject.localizationFunctor_map_isIso_of_preStep
      arrow denominator.1

/-- The canonical comparison from the generic categorical localization to
the model's explicit filtered-Hom-colimit localization. -/
def genericToColimitComparison :
    FrobenioidBirationalization.BirationalCategory
        (sourcePresentation data baseTotallyEpimorphic) ⥤
      SourceModelFrobenioid.Carrier.ColimitBirationalObject
        (Phi := Phi) (data := data) :=
  Localization.Construction.lift
    (SourceModelFrobenioid.Carrier.ColimitBirationalObject.localizationFunctor
      (Phi := Phi) (data := data))
    (colimitLocalization_inverts data baseTotallyEpimorphic)

/-- The comparison extends the same canonical localization of the Theorem
5.2 source. -/
theorem genericToColimitComparison_fac :
    FrobenioidBirationalization.localizationFunctor
          (sourcePresentation data baseTotallyEpimorphic) ⋙
        genericToColimitComparison data baseTotallyEpimorphic =
      SourceModelFrobenioid.Carrier.ColimitBirationalObject.localizationFunctor
        (Phi := Phi) (data := data) :=
  Localization.Construction.fac _ _

/-- Tautological conversion from the generic presentation of `F_(Phi^gp)`
to the earlier model presentation, whose divisor field is a member of the
full subgroup. -/
def genericAmbientToModelAmbient :
    FrobenioidBirationalization.GroupifiedElementaryFrobenioid Phi ⥤
      SourceModelFrobenioid.GroupifiedElementaryFrobenioid
        (SourceModelFrobenioid.GroupifiedDivisorSubfunctor.full Phi) where
  obj object := ⟨object.base⟩
  map arrow :=
    { base := arrow.base
      divisor := ⟨arrow.divisor, trivial⟩
      frobeniusDegree := arrow.frobeniusDegree }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- On the source model, the two presentations of the groupified structure
functor agree after the ambient conversion. -/
theorem groupifiedStructureFunctor_comparison :
    FrobenioidBirationalization.groupifiedStructureFunctor
          (sourcePresentation data baseTotallyEpimorphic) ⋙
        genericAmbientToModelAmbient (Phi := Phi) =
      SourceModelFrobenioid.Carrier.groupifiedStructureFunctor
        (Phi := Phi) (data := data) := by
  rfl

omit [IsConnected D] in
/-- The model comparison functor identifies its filtered-colimit
localization with its concrete birational-object implementation. -/
theorem modelLocalizationComparison :
    SourceModelFrobenioid.Carrier.ColimitBirationalObject.localizationFunctor
          (Phi := Phi) (data := data) ⋙
        SourceModelFrobenioid.Carrier.ColimitBirationalObject.comparisonFunctor =
      SourceModelFrobenioid.BirationalObject.inclusionFunctor := by
  apply CategoryTheory.Functor.hext
  · intro object
    rfl
  · intro source target arrow
    exact heq_of_eq
      (comparisonFunctor_map_localizationFunctor arrow)

/-- The model's source comparison, expressed against the actual
filtered-colimit divisor functor rather than its equivalent concrete target. -/
def modelColimitStructureComparison :
    SourceModelFrobenioid.Carrier.groupifiedStructureFunctor
        (Phi := Phi) (data := data) ≅
      SourceModelFrobenioid.Carrier.ColimitBirationalObject.localizationFunctor
          (Phi := Phi) (data := data) ⋙
        SourceModelFrobenioid.Carrier.ColimitBirationalObject.groupifiedDivisorFunctor :=
  SourceModelFrobenioid.Carrier.groupifiedStructureComparison ≪≫
    (eqToIso (by
      rw [SourceModelFrobenioid.Carrier.ColimitBirationalObject.groupifiedDivisorFunctor,
        ← Functor.assoc,
        modelLocalizationComparison data])).symm

/-- The generic raw groupified functor, converted to the model's ambient
elementary category. -/
def genericGroupifiedDivisorFunctor :
    FrobenioidBirationalization.BirationalCategory
        (sourcePresentation data baseTotallyEpimorphic) ⥤
      SourceModelFrobenioid.GroupifiedElementaryFrobenioid
        (SourceModelFrobenioid.GroupifiedDivisorSubfunctor.full Phi) :=
  FrobenioidBirationalization.groupifiedBirationalFunctor
      (sourcePresentation data baseTotallyEpimorphic) ⋙
    genericAmbientToModelAmbient (Phi := Phi)

/-- The existing model divisor functor pulled back along the canonical
generic-to-colimit comparison. -/
def colimitModelGroupifiedDivisorFunctor :
    FrobenioidBirationalization.BirationalCategory
        (sourcePresentation data baseTotallyEpimorphic) ⥤
      SourceModelFrobenioid.GroupifiedElementaryFrobenioid
        (SourceModelFrobenioid.GroupifiedDivisorSubfunctor.full Phi) :=
  genericToColimitComparison data baseTotallyEpimorphic ⋙
    SourceModelFrobenioid.Carrier.ColimitBirationalObject.groupifiedDivisorFunctor

/-- The generic raw divisor functor is a lift of the converted source
structure functor. -/
def genericGroupifiedDivisorFunctor_fac :
    FrobenioidBirationalization.localizationFunctor
          (sourcePresentation data baseTotallyEpimorphic) ⋙
        genericGroupifiedDivisorFunctor data baseTotallyEpimorphic ≅
      FrobenioidBirationalization.groupifiedStructureFunctor
          (sourcePresentation data baseTotallyEpimorphic) ⋙
        genericAmbientToModelAmbient (Phi := Phi) :=
  eqToIso (by
    rw [genericGroupifiedDivisorFunctor, ← Functor.assoc,
      FrobenioidBirationalization.groupifiedBirationalFunctor_fac])

/-- The pulled-back model divisor functor is a lift of the model source
structure functor. -/
def colimitModelGroupifiedDivisorFunctor_fac :
    FrobenioidBirationalization.localizationFunctor
          (sourcePresentation data baseTotallyEpimorphic) ⋙
        colimitModelGroupifiedDivisorFunctor data baseTotallyEpimorphic ≅
      SourceModelFrobenioid.Carrier.groupifiedStructureFunctor
        (Phi := Phi) (data := data) :=
  eqToIso (by
    rw [colimitModelGroupifiedDivisorFunctor, ← Functor.assoc,
      genericToColimitComparison_fac data baseTotallyEpimorphic]
    rfl) ≪≫
    (modelColimitStructureComparison data).symm

/-- The existing Theorem 5.2 divisor implementation is the specialization
of the generic Proposition 4.4 construction: after the canonical localization
and ambient comparisons, their raw groupified functors are naturally
isomorphic. -/
def groupifiedDivisorFunctor_specializationIso :
    genericGroupifiedDivisorFunctor data baseTotallyEpimorphic ≅
      colimitModelGroupifiedDivisorFunctor data baseTotallyEpimorphic := by
  let genericSource :=
    FrobenioidBirationalization.groupifiedStructureFunctor
        (sourcePresentation data baseTotallyEpimorphic) ⋙
      genericAmbientToModelAmbient (Phi := Phi)
  let modelSource :=
    SourceModelFrobenioid.Carrier.groupifiedStructureFunctor
      (Phi := Phi) (data := data)
  letI : Localization.Lifting
      (FrobenioidBirationalization.localizationFunctor
        (sourcePresentation data baseTotallyEpimorphic))
      (FrobenioidBirationalization.denominators
        (sourcePresentation data baseTotallyEpimorphic))
      genericSource
      (genericGroupifiedDivisorFunctor data baseTotallyEpimorphic) :=
    ⟨genericGroupifiedDivisorFunctor_fac data baseTotallyEpimorphic⟩
  letI : Localization.Lifting
      (FrobenioidBirationalization.localizationFunctor
        (sourcePresentation data baseTotallyEpimorphic))
      (FrobenioidBirationalization.denominators
        (sourcePresentation data baseTotallyEpimorphic))
      modelSource
      (colimitModelGroupifiedDivisorFunctor data baseTotallyEpimorphic) :=
    ⟨colimitModelGroupifiedDivisorFunctor_fac data baseTotallyEpimorphic⟩
  exact Localization.liftNatIso
    (FrobenioidBirationalization.localizationFunctor
      (sourcePresentation data baseTotallyEpimorphic))
    (FrobenioidBirationalization.denominators
      (sourcePresentation data baseTotallyEpimorphic))
    genericSource modelSource
    (genericGroupifiedDivisorFunctor data baseTotallyEpimorphic)
    (colimitModelGroupifiedDivisorFunctor data baseTotallyEpimorphic)
    (eqToIso (groupifiedStructureFunctor_comparison data
      baseTotallyEpimorphic))

/-- The generic restricted factor itself recovers the existing model lower
route after inclusion into `Phi^gp`.  This is the complete specialization of
the Proposition 4.4(iii) 1-commutative diagram. -/
def restrictedFactor_specializationIso :
    (FrobenioidBirationalization.birationalRestrictedFactorFunctor
          (sourcePresentation data baseTotallyEpimorphic) ⋙
        FrobenioidBirationalization.birationalRestrictedElementaryInclusion
          (sourcePresentation data baseTotallyEpimorphic)) ⋙
      genericAmbientToModelAmbient (Phi := Phi) ≅
    colimitModelGroupifiedDivisorFunctor data baseTotallyEpimorphic :=
  ((Functor.whiskeringRight _ _ _).obj
      (genericAmbientToModelAmbient (Phi := Phi))).mapIso
        (FrobenioidBirationalization.birationalRestrictedFactorIso
          (sourcePresentation data baseTotallyEpimorphic)) ≪≫
    groupifiedDivisorFunctor_specializationIso data baseTotallyEpimorphic

end

end Iut.SourceModelFrobenioid.GenericBirationalSpecialization
