/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

/-!
  # Arithmetic-only primitives shared by the source clauses

  `InitialThetaArithmeticData` contains enough information to construct a
  canonical algebraic closure, the absolute-Galois carrier used by the
  orbicurve records, the full restriction section on finite and infinite
  places, and the K/F torsion transport.  It does not contain the source
  conditions which are needed for the six clauses.  This file records exactly
  the former objects so that later source constructions do not repeat them or
  replace them with an unrelated carrier.

  The construction is deliberately a small prelude.  In particular, it does
  not choose a bad-place set, a q-parameter, an orbicurve, a finite-etale
  fundamental group, a large-image basis, or a boundary cusp.
 -/

namespace LeanFormal.IUT

universe u

noncomputable section

namespace InitialThetaSource

structure SourceArithmeticPrelude
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l) where
  placeSection : NumberFieldPlace.RestrictionSection A.Fmod A.K

namespace SourceArithmeticPrelude

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}

noncomputable def fbar (_P : SourceArithmeticPrelude A) :
    SourceFbarExtension.{u} A :=
  SourceFbarExtension.canonical A

noncomputable def torsionTransport (_P : SourceArithmeticPrelude A) :
    (A.curve.baseChange A.K).LTorsion l ≃ₗ[ZMod l.value] A.curve.LTorsion l :=
  PuncturedEllipticCurve.initialThetaKToFTorsionTransport A

abbrev absoluteGalois : ProfiniteGrp.{u} := Iut.AbsoluteGaloisProfinite A.F

def selectedPlaces (P : SourceArithmeticPrelude A) :
    Set (NumberFieldPlace A.K) :=
  P.placeSection.selected

noncomputable def selectedEquiv (P : SourceArithmeticPrelude A) :
    NumberFieldPlace A.Fmod ≃
      {v : NumberFieldPlace A.K // v ∈ P.selectedPlaces} :=
  P.placeSection.selectedEquiv

def selectedNonarchimedean (P : SourceArithmeticPrelude A) :
    Set {v : NumberFieldPlace A.K // v ∈ P.selectedPlaces} :=
  {v | NumberFieldPlace.IsFinite v.1}

def selectedArchimedean (P : SourceArithmeticPrelude A) :
    Set {v : NumberFieldPlace A.K // v ∈ P.selectedPlaces} :=
  {v | NumberFieldPlace.IsInfinite v.1}

noncomputable def canonical (A : InitialThetaArithmeticData.{u} l) :
    SourceArithmeticPrelude A where
  placeSection := NumberFieldPlace.restrictionSection

noncomputable def fromPlaceSection
    (A : InitialThetaArithmeticData.{u} l)
    (placeSelection : NumberFieldPlace.RestrictionSection A.Fmod A.K) :
    SourceArithmeticPrelude A where
  placeSection := placeSelection

@[simp] theorem fromPlaceSection_placeSection
    (A : InitialThetaArithmeticData.{u} l)
    (placeSelection : NumberFieldPlace.RestrictionSection A.Fmod A.K) :
    (fromPlaceSection A placeSelection).placeSection = placeSelection :=
  rfl

@[simp] theorem fromPlaceSection_fbar
    (A : InitialThetaArithmeticData.{u} l)
    (placeSelection : NumberFieldPlace.RestrictionSection A.Fmod A.K) :
    (fromPlaceSection A placeSelection).fbar = SourceFbarExtension.canonical A :=
  rfl

@[simp] theorem fromPlaceSection_torsionTransport
    (A : InitialThetaArithmeticData.{u} l)
    (placeSelection : NumberFieldPlace.RestrictionSection A.Fmod A.K) :
    (fromPlaceSection A placeSelection).torsionTransport =
      PuncturedEllipticCurve.initialThetaKToFTorsionTransport A :=
  rfl

@[simp] theorem canonical_fbar
    (A : InitialThetaArithmeticData.{u} l) :
    (canonical A).fbar = SourceFbarExtension.canonical A :=
  rfl

@[simp] theorem canonical_placeSection
    (A : InitialThetaArithmeticData.{u} l) :
    (canonical A).placeSection = NumberFieldPlace.restrictionSection :=
  rfl

@[simp] theorem canonical_torsionTransport
    (A : InitialThetaArithmeticData.{u} l) :
    (canonical A).torsionTransport =
      PuncturedEllipticCurve.initialThetaKToFTorsionTransport A :=
  rfl

theorem fbar_is_algebraically_closed (P : SourceArithmeticPrelude A) :
    IsAlgClosed P.fbar.carrier :=
  P.fbar.carrier_is_algClosed

theorem fbar_is_algebraic (P : SourceArithmeticPrelude A) (x : P.fbar.carrier) :
    IsAlgebraic A.F x :=
  P.fbar.carrier_is_algebraic x

noncomputable def fbar_comparison (P : SourceArithmeticPrelude A) :
    P.fbar.carrier ≃ₐ[A.F] AlgebraicClosure A.F :=
  P.fbar.comparison

theorem placeSection_comap_lift
    (P : SourceArithmeticPrelude A) (v : NumberFieldPlace A.Fmod) :
    NumberFieldPlace.comap (k := A.Fmod) (P.placeSection.lift v) = v :=
  P.placeSection.comap_lift v

theorem placeSection_lift_injective
    (P : SourceArithmeticPrelude A) :
    Function.Injective P.placeSection.lift :=
  P.placeSection.lift_injective

theorem selectedPlaces_eq_range
    (P : SourceArithmeticPrelude A) :
    P.selectedPlaces = Set.range P.placeSection.lift :=
  rfl

theorem selectedEquiv_apply
    (P : SourceArithmeticPrelude A) (v : NumberFieldPlace A.Fmod) :
    (P.selectedEquiv v).1 = P.placeSection.lift v :=
  rfl

theorem selectedEquiv_left_inverse
    (P : SourceArithmeticPrelude A) (v : NumberFieldPlace A.Fmod) :
    P.selectedEquiv.symm (P.selectedEquiv v) = v :=
  P.selectedEquiv.left_inv v

theorem selectedEquiv_right_inverse
    (P : SourceArithmeticPrelude A)
    (v : {v : NumberFieldPlace A.K // v ∈ P.selectedPlaces}) :
    P.selectedEquiv (P.selectedEquiv.symm v) = v :=
  P.selectedEquiv.right_inv v

theorem selectedEquiv_symm_apply
    (P : SourceArithmeticPrelude A)
    (v : {v : NumberFieldPlace A.K // v ∈ P.selectedPlaces}) :
    P.selectedEquiv.symm v =
      NumberFieldPlace.comap (k := A.Fmod) v.1 :=
  NumberFieldPlace.RestrictionSection.selectedEquiv_symm_apply
    P.placeSection v

theorem selected_place_comap
    (P : SourceArithmeticPrelude A)
    (v : {v : NumberFieldPlace A.K // v ∈ P.selectedPlaces}) :
    NumberFieldPlace.comap (k := A.Fmod) v.1 =
      P.selectedEquiv.symm v := by
  symm
  exact P.selectedEquiv_symm_apply v

theorem selected_nonarchimedean_or_archimedean_cover
    (P : SourceArithmeticPrelude A) :
    P.selectedNonarchimedean ∪ P.selectedArchimedean = Set.univ := by
  ext v
  rcases v with ⟨place, hv⟩
  cases place with
  | finite w =>
      simp [selectedNonarchimedean, selectedArchimedean,
        NumberFieldPlace.IsFinite, NumberFieldPlace.IsInfinite]
  | infinite w =>
      simp [selectedNonarchimedean, selectedArchimedean,
        NumberFieldPlace.IsFinite, NumberFieldPlace.IsInfinite]

theorem selected_nonarchimedean_archimedean_disjoint
    (P : SourceArithmeticPrelude A) :
    Disjoint P.selectedNonarchimedean P.selectedArchimedean := by
  rw [Set.disjoint_left]
  rintro ⟨place, hv⟩ hvnon hvarc
  cases place with
  | finite w =>
      exact NumberFieldPlace.not_isInfinite_finite w
        (by
          simp [selectedArchimedean, NumberFieldPlace.IsInfinite] at hvarc)
  | infinite w =>
      exact NumberFieldPlace.not_isFinite_infinite w
        (by
          simp [selectedNonarchimedean, NumberFieldPlace.IsFinite] at hvnon)

theorem selected_nonarchimedean_spec
    (P : SourceArithmeticPrelude A)
    (v : {v : NumberFieldPlace A.K // v ∈ P.selectedPlaces}) :
    v ∈ P.selectedNonarchimedean ↔ NumberFieldPlace.IsFinite v.1 :=
  Iff.rfl

theorem selected_archimedean_spec
    (P : SourceArithmeticPrelude A)
    (v : {v : NumberFieldPlace A.K // v ∈ P.selectedPlaces}) :
    v ∈ P.selectedArchimedean ↔ NumberFieldPlace.IsInfinite v.1 :=
  Iff.rfl

theorem selected_finite_lift_mem
    (P : SourceArithmeticPrelude A)
    (p : NumberField.FinitePlace A.Fmod) :
    (P.selectedEquiv (NumberFieldPlace.finite p)).1 ∈ P.selectedPlaces := by
  exact (P.selectedEquiv (NumberFieldPlace.finite p)).2

theorem selected_infinite_lift_mem
    (P : SourceArithmeticPrelude A)
    (v : NumberField.InfinitePlace A.Fmod) :
    (P.selectedEquiv (NumberFieldPlace.infinite v)).1 ∈ P.selectedPlaces := by
  exact (P.selectedEquiv (NumberFieldPlace.infinite v)).2

theorem selected_finite_lift_is_finite
    (P : SourceArithmeticPrelude A)
    (p : NumberField.FinitePlace A.Fmod) :
    P.selectedEquiv (NumberFieldPlace.finite p) ∈
      P.selectedNonarchimedean := by
  change NumberFieldPlace.IsFinite
    (P.selectedEquiv (NumberFieldPlace.finite p)).1
  rw [P.selectedEquiv_apply]
  cases hLift : P.placeSection.lift (NumberFieldPlace.finite p) with
  | finite q =>
      simp [NumberFieldPlace.IsFinite]
  | infinite q =>
      have hComap := P.placeSection.comap_lift (NumberFieldPlace.finite p)
      rw [hLift] at hComap
      simp only [NumberFieldPlace.comap_infinite] at hComap
      cases hComap

theorem selected_infinite_lift_is_archimedean
    (P : SourceArithmeticPrelude A)
    (v : NumberField.InfinitePlace A.Fmod) :
    P.selectedEquiv (NumberFieldPlace.infinite v) ∈
      P.selectedArchimedean := by
  change NumberFieldPlace.IsInfinite
    (P.selectedEquiv (NumberFieldPlace.infinite v)).1
  rw [P.selectedEquiv_apply]
  cases hLift : P.placeSection.lift (NumberFieldPlace.infinite v) with
  | finite q =>
      have hComap := P.placeSection.comap_lift (NumberFieldPlace.infinite v)
      rw [hLift] at hComap
      simp only [NumberFieldPlace.comap_finite] at hComap
      cases hComap
  | infinite q =>
      simp [NumberFieldPlace.IsInfinite]

theorem torsionTransport_bijective
    (P : SourceArithmeticPrelude A) :
    Function.Bijective P.torsionTransport :=
  P.torsionTransport.bijective

theorem canonical_torsionTransport_bijective
    (A : InitialThetaArithmeticData.{u} l) :
    Function.Bijective (canonical A).torsionTransport :=
  (canonical A).torsionTransport_bijective

theorem fbar_comparison_injective (P : SourceArithmeticPrelude A) :
    Function.Injective P.fbar.comparison :=
  P.fbar.comparison.injective

theorem fbar_comparison_surjective (P : SourceArithmeticPrelude A) :
    Function.Surjective P.fbar.comparison :=
  P.fbar.comparison.surjective

theorem selectedPlaces_eq_section (P : SourceArithmeticPrelude A) :
    P.selectedPlaces = P.placeSection.selected :=
  rfl

theorem selectedEquiv_bijective (P : SourceArithmeticPrelude A) :
    Function.Bijective P.selectedEquiv :=
  P.selectedEquiv.bijective

theorem selected_finite_lift_comap
    (P : SourceArithmeticPrelude A)
    (p : NumberField.FinitePlace A.Fmod) :
    NumberFieldPlace.comap (k := A.Fmod)
        (P.selectedEquiv (NumberFieldPlace.finite p)).1 =
      NumberFieldPlace.finite p :=
  P.placeSection.comap_lift (NumberFieldPlace.finite p)

theorem selected_infinite_lift_comap
    (P : SourceArithmeticPrelude A)
    (v : NumberField.InfinitePlace A.Fmod) :
    NumberFieldPlace.comap (k := A.Fmod)
        (P.selectedEquiv (NumberFieldPlace.infinite v)).1 =
      NumberFieldPlace.infinite v :=
  P.placeSection.comap_lift (NumberFieldPlace.infinite v)

theorem selected_finite_lift_is_not_infinite
    (P : SourceArithmeticPrelude A)
    (p : NumberField.FinitePlace A.Fmod) :
    ¬ NumberFieldPlace.IsInfinite
        (P.selectedEquiv (NumberFieldPlace.finite p)).1 := by
  intro hinfinite
  have hfinite := P.selected_finite_lift_is_finite p
  change NumberFieldPlace.IsFinite
    (P.selectedEquiv (NumberFieldPlace.finite p)).1 at hfinite
  cases hplace : (P.selectedEquiv (NumberFieldPlace.finite p)).1 with
  | finite q =>
      rw [hplace] at hinfinite
      exact NumberFieldPlace.not_isInfinite_finite q hinfinite
  | infinite q =>
      rw [hplace] at hfinite
      exact NumberFieldPlace.not_isFinite_infinite q hfinite

theorem selected_infinite_lift_is_not_finite
    (P : SourceArithmeticPrelude A)
    (v : NumberField.InfinitePlace A.Fmod) :
    ¬ NumberFieldPlace.IsFinite
        (P.selectedEquiv (NumberFieldPlace.infinite v)).1 := by
  intro hfinite
  have hinfinite := P.selected_infinite_lift_is_archimedean v
  change NumberFieldPlace.IsInfinite
    (P.selectedEquiv (NumberFieldPlace.infinite v)).1 at hinfinite
  cases hplace : (P.selectedEquiv (NumberFieldPlace.infinite v)).1 with
  | finite q =>
      rw [hplace] at hinfinite
      exact NumberFieldPlace.not_isInfinite_finite q hinfinite
  | infinite q =>
      exact NumberFieldPlace.not_isFinite_infinite q
        (by
          rw [hplace] at hfinite
          exact hfinite)

theorem selected_place_kind_partition
    (P : SourceArithmeticPrelude A) :
    (∀ v : {v : NumberFieldPlace A.K // v ∈ P.selectedPlaces},
      v ∈ P.selectedNonarchimedean ∨ v ∈ P.selectedArchimedean) ∧
      (∀ v : {v : NumberFieldPlace A.K // v ∈ P.selectedPlaces},
        ¬ (v ∈ P.selectedNonarchimedean ∧
          v ∈ P.selectedArchimedean)) := by
  constructor
  · intro v
    have hcover := congrArg (fun s => v ∈ s)
      P.selected_nonarchimedean_or_archimedean_cover
    simpa [Set.mem_union] using hcover.mpr trivial
  · intro v hv
    exact Set.disjoint_left.mp
      P.selected_nonarchimedean_archimedean_disjoint hv.1 hv.2

theorem torsionTransport_left_inverse (P : SourceArithmeticPrelude A) :
    Function.LeftInverse P.torsionTransport.symm P.torsionTransport :=
  fun x => P.torsionTransport.symm_apply_apply x

theorem torsionTransport_right_inverse (P : SourceArithmeticPrelude A) :
    Function.RightInverse P.torsionTransport.symm P.torsionTransport :=
  fun x => P.torsionTransport.apply_symm_apply x

theorem canonical_selectedPlaces
    (A : InitialThetaArithmeticData.{u} l) :
    (canonical A).selectedPlaces =
      (NumberFieldPlace.restrictionSection
        (k := A.Fmod) (K := A.K)).selected :=
  rfl

theorem fromPlaceSection_selectedPlaces
    (A : InitialThetaArithmeticData.{u} l)
    (placeSelection : NumberFieldPlace.RestrictionSection A.Fmod A.K) :
    (fromPlaceSection A placeSelection).selectedPlaces =
      placeSelection.selected :=
  rfl

theorem fromPlaceSection_selectedEquiv
    (A : InitialThetaArithmeticData.{u} l)
    (placeSelection : NumberFieldPlace.RestrictionSection A.Fmod A.K) :
    (fromPlaceSection A placeSelection).selectedEquiv =
      placeSelection.selectedEquiv :=
  rfl

theorem fromPlaceSection_selectedEquiv_bijective
    (A : InitialThetaArithmeticData.{u} l)
    (placeSelection : NumberFieldPlace.RestrictionSection A.Fmod A.K) :
    Function.Bijective
      (fromPlaceSection A placeSelection).selectedEquiv :=
  (fromPlaceSection A placeSelection).selectedEquiv_bijective

theorem exists_canonical (l : PrimeGeFive) :
    ∀ A : InitialThetaArithmeticData.{u} l,
      Nonempty (SourceArithmeticPrelude A) := by
  intro A
  exact ⟨canonical A⟩

noncomputable def canonical_fbar_comparison_to_any
    (A : InitialThetaArithmeticData.{u} l)
    (P : SourceArithmeticPrelude A) :
    P.fbar.carrier ≃ₐ[A.F] (canonical A).fbar.carrier := by
  change P.fbar.carrier ≃ₐ[A.F] AlgebraicClosure A.F
  exact P.fbar.comparison

end SourceArithmeticPrelude

end InitialThetaSource

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def initialThetaArithmeticPrelude : Obligation :=
  { id := "IUT-I.definition-3.1-A2-arithmetic-prelude"
    source := "IUT I, Definition 3.1 arithmetic carriers and place notation"
    status := VerificationStatus.provedKernel
    note :=
      "InitialThetaArithmeticData canonically supplies the algebraic closure, " ++
        "the absolute-Galois profinite carrier, the full finite/infinite place " ++
        "restriction section, and the constructed K/F torsion transport. " ++
        "The prelude does not supply any of clauses (a)-(f)."
    dependsOn :=
      [ "IUT-I.initial-theta-arithmetic-data",
        "Foundations.NumberField.places",
        "IUT-I.initial-theta-k-f-torsion-transport" ] }

end LeanFormal.IUT.Audit
