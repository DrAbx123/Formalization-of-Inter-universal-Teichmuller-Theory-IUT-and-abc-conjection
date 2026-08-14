/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.Foundations.NumberField.Places

/-!
  # The selected-place part of the source boundary

  `NumberFieldPlace.restrictionSection` is an actual construction in the
  foundations: it chooses one finite or infinite extension above every place
  of the lower number field, and proves that restriction is a left inverse.
  The source tuple still has to supply the bad-place set and its arithmetic
  properties.  `SourcePlaceSelection` packages exactly that remaining source
  condition and derives all section-dependent fields from the canonical
  restriction section.

  This record does not assert that a chosen bad place has bad reduction, nor
  that its residue characteristic is coprime to `l`; those are Clause (b)
  conditions and remain separate.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

namespace InitialThetaSource

structure SourcePlaceSelection
    {l : PrimeGeFive} (A : InitialThetaArithmeticData l) where
  V_mod_bad : Set (NumberField.FinitePlace A.Fmod)
  V_mod_bad_odd_residue_characteristic :
    ∀ p, p ∈ V_mod_bad →
      Odd (NumberFieldFinitePlace.residueCharacteristic p)
  V_mod_bad_nonempty : V_mod_bad.Nonempty

/-! A singleton bad-place set can be built when the source supplies one finite
    place of odd residue characteristic.  The constructor proves exactly the
    set-theoretic fields of this record; it does not assert that the curve has
    bad or multiplicative reduction at the chosen place. -/
def SourcePlaceSelection.singleton
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (p : NumberField.FinitePlace A.Fmod)
    (hodd : Odd (NumberFieldFinitePlace.residueCharacteristic p)) :
    SourcePlaceSelection A where
  V_mod_bad := {p}
  V_mod_bad_odd_residue_characteristic := by
    intro q hq
    have hqp : q = p := by simpa using hq
    rw [hqp]
    exact hodd
  V_mod_bad_nonempty := ⟨p, by simp⟩

@[simp] theorem SourcePlaceSelection.singleton_V_mod_bad
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (p : NumberField.FinitePlace A.Fmod)
    (hodd : Odd (NumberFieldFinitePlace.residueCharacteristic p)) :
    (SourcePlaceSelection.singleton A p hodd).V_mod_bad = {p} :=
  rfl

theorem SourcePlaceSelection.singleton_bad_place_odd
    {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l)
    (p : NumberField.FinitePlace A.Fmod)
    (hodd : Odd (NumberFieldFinitePlace.residueCharacteristic p)) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  hodd

namespace SourcePlaceSelection

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData l}

noncomputable def V_section
    (_P : SourcePlaceSelection A) :
    NumberFieldPlace.RestrictionSection A.Fmod A.K :=
  NumberFieldPlace.restrictionSection

def V
    (P : SourcePlaceSelection A) : Set (NumberFieldPlace A.K) :=
  P.V_section.selected

def V_mod_good
    (P : SourcePlaceSelection A) : Set (NumberFieldPlace A.Fmod) :=
  Set.univ \ (NumberFieldPlace.finite '' P.V_mod_bad)

def V_non
    (P : SourcePlaceSelection A) :
    Set {v : NumberFieldPlace A.K // v ∈ P.V} :=
  {v | NumberFieldPlace.IsFinite v.1}

def V_arc
    (P : SourcePlaceSelection A) :
    Set {v : NumberFieldPlace A.K // v ∈ P.V} :=
  {v | NumberFieldPlace.IsInfinite v.1}

noncomputable def V_mod_bijection
    (P : SourcePlaceSelection A) :
    NumberFieldPlace A.Fmod ≃
      {v : NumberFieldPlace A.K // v ∈ P.V} :=
  P.V_section.selectedEquiv

def V_bad
    (P : SourcePlaceSelection A) :
    Set {v : NumberFieldPlace A.K // v ∈ P.V} :=
  {v | P.V_mod_bijection.symm v ∈ NumberFieldPlace.finite '' P.V_mod_bad}

def V_good
    (P : SourcePlaceSelection A) :
    Set {v : NumberFieldPlace A.K // v ∈ P.V} :=
  {v | P.V_mod_bijection.symm v ∉ NumberFieldPlace.finite '' P.V_mod_bad}

theorem V_eq_section
    (P : SourcePlaceSelection A) :
    P.V = P.V_section.selected :=
  rfl

theorem V_mod_bijection_apply
    (P : SourcePlaceSelection A) (v : NumberFieldPlace A.Fmod) :
    (P.V_mod_bijection v).1 = P.V_section.lift v :=
  rfl

theorem V_mod_good_eq_compl_bad
    (P : SourcePlaceSelection A) :
    P.V_mod_good =
      (NumberFieldPlace.finite '' P.V_mod_bad)ᶜ := by
  ext v
  simp [V_mod_good]

theorem V_mod_bad_or_good_cover
    (P : SourcePlaceSelection A) :
    NumberFieldPlace.finite '' P.V_mod_bad ∪ P.V_mod_good = Set.univ := by
  ext v
  simp [V_mod_good]

theorem V_mod_bad_or_good_disjoint
    (P : SourcePlaceSelection A) :
    Disjoint (NumberFieldPlace.finite '' P.V_mod_bad) P.V_mod_good := by
  rw [Set.disjoint_left]
  intro v hvbad hvgood
  have hnot : v ∉ NumberFieldPlace.finite '' P.V_mod_bad := by
    simpa [V_mod_good] using hvgood
  exact hnot hvbad

theorem V_mod_bijection_symm_apply
    (P : SourcePlaceSelection A)
    (v : {v : NumberFieldPlace A.K // v ∈ P.V}) :
    P.V_mod_bijection.symm v =
      NumberFieldPlace.comap (k := A.Fmod) v.1 :=
  NumberFieldPlace.RestrictionSection.selectedEquiv_symm_apply
    P.V_section v

theorem V_place_comap
    (P : SourcePlaceSelection A)
    (v : {v : NumberFieldPlace A.K // v ∈ P.V}) :
    NumberFieldPlace.comap (k := A.Fmod) v.1 =
      P.V_mod_bijection.symm v := by
  symm
  exact P.V_mod_bijection_symm_apply v

theorem V_non_or_arc_cover
    (P : SourcePlaceSelection A) :
    P.V_non ∪ P.V_arc = Set.univ := by
  ext v
  rcases v with ⟨place, hv⟩
  cases place with
  | finite w => simp [V_non, V_arc, NumberFieldPlace.IsFinite,
      NumberFieldPlace.IsInfinite]
  | infinite w => simp [V_non, V_arc, NumberFieldPlace.IsFinite,
      NumberFieldPlace.IsInfinite]

theorem V_non_or_arc_disjoint
    (P : SourcePlaceSelection A) :
    Disjoint P.V_non P.V_arc := by
  rw [Set.disjoint_left]
  rintro ⟨place, hv⟩ hvnon hvarc
  cases place with
  | finite w =>
      exact NumberFieldPlace.not_isInfinite_finite w
        (by
          simp [V_arc, NumberFieldPlace.IsInfinite] at hvarc)
  | infinite w =>
      exact NumberFieldPlace.not_isFinite_infinite w
        (by
          simp [V_non, NumberFieldPlace.IsFinite] at hvnon)

theorem V_bad_or_good_cover
  (P : SourcePlaceSelection A) :
    P.V_bad ∪ P.V_good = Set.univ := by
  ext v
  change (P.V_mod_bijection.symm v ∈
      NumberFieldPlace.finite '' P.V_mod_bad ∨
      P.V_mod_bijection.symm v ∉
        NumberFieldPlace.finite '' P.V_mod_bad) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    exact Classical.em _

theorem V_bad_or_good_disjoint
    (P : SourcePlaceSelection A) :
    Disjoint P.V_bad P.V_good := by
  rw [Set.disjoint_left]
  intro v hvbad hvgood
  exact hvgood hvbad

theorem V_bad_finite_spec
    (P : SourcePlaceSelection A)
    (v : {v : NumberFieldPlace A.K // v ∈ P.V}) :
    v ∈ P.V_bad ↔
      P.V_mod_bijection.symm v ∈ NumberFieldPlace.finite '' P.V_mod_bad :=
  Iff.rfl

theorem V_good_spec
    (P : SourcePlaceSelection A)
    (v : {v : NumberFieldPlace A.K // v ∈ P.V}) :
    v ∈ P.V_good ↔
      P.V_mod_bijection.symm v ∉ NumberFieldPlace.finite '' P.V_mod_bad :=
  Iff.rfl

theorem V_non_spec
    (P : SourcePlaceSelection A)
    (v : {v : NumberFieldPlace A.K // v ∈ P.V}) :
    v ∈ P.V_non ↔ NumberFieldPlace.IsFinite v.1 :=
  Iff.rfl

theorem V_arc_spec
    (P : SourcePlaceSelection A)
    (v : {v : NumberFieldPlace A.K // v ∈ P.V}) :
    v ∈ P.V_arc ↔ NumberFieldPlace.IsInfinite v.1 :=
  Iff.rfl

theorem V_mod_bad_odd_residue_characteristic_spec
    (P : SourcePlaceSelection A) (p : NumberField.FinitePlace A.Fmod)
    (hp : p ∈ P.V_mod_bad) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  P.V_mod_bad_odd_residue_characteristic p hp

theorem V_mod_bad_nonempty_spec
    (P : SourcePlaceSelection A) : P.V_mod_bad.Nonempty :=
  P.V_mod_bad_nonempty

theorem selected_place_comap_left_inverse
    (P : SourcePlaceSelection A) (v : NumberFieldPlace A.Fmod) :
    NumberFieldPlace.comap (k := A.Fmod) (P.V_section.lift v) = v :=
  P.V_section.comap_lift v

theorem selected_place_lift_injective
    (P : SourcePlaceSelection A) :
    Function.Injective P.V_section.lift :=
  P.V_section.lift_injective

theorem selected_finite_place
    (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    P.V_section.lift (NumberFieldPlace.finite p) ∈ P.V := by
  exact ⟨NumberFieldPlace.finite p, rfl⟩

theorem selected_infinite_place
    (P : SourcePlaceSelection A)
    (v : NumberField.InfinitePlace A.Fmod) :
    P.V_section.lift (NumberFieldPlace.infinite v) ∈ P.V := by
  exact ⟨NumberFieldPlace.infinite v, rfl⟩

theorem selected_equiv_left_inverse
    (P : SourcePlaceSelection A) (v : NumberFieldPlace A.Fmod) :
    P.V_mod_bijection.symm (P.V_mod_bijection v) = v :=
  P.V_mod_bijection.left_inv v

theorem selected_equiv_right_inverse
    (P : SourcePlaceSelection A)
    (v : {v : NumberFieldPlace A.K // v ∈ P.V}) :
    P.V_mod_bijection (P.V_mod_bijection.symm v) = v :=
  P.V_mod_bijection.right_inv v

/-! A bad moduli place has a canonical selected place above it.  These lemmas
    keep the upper place and its comap tied to the same restriction section. -/
theorem selected_bad_place_mem
    (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod)
    (hp : p ∈ P.V_mod_bad) :
    P.V_mod_bijection (NumberFieldPlace.finite p) ∈ P.V_bad := by
  change P.V_mod_bijection.symm
      (P.V_mod_bijection (NumberFieldPlace.finite p)) ∈
    NumberFieldPlace.finite '' P.V_mod_bad
  have hleft :
      P.V_mod_bijection.symm
          (P.V_mod_bijection (NumberFieldPlace.finite p)) =
        NumberFieldPlace.finite p :=
    P.V_mod_bijection.left_inv (NumberFieldPlace.finite p)
  rw [hleft]
  exact ⟨p, hp, rfl⟩

theorem selected_bad_place_is_finite
    (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod)
    (_hp : p ∈ P.V_mod_bad) :
    P.V_mod_bijection (NumberFieldPlace.finite p) ∈ P.V_non := by
  change NumberFieldPlace.IsFinite
    (P.V_mod_bijection (NumberFieldPlace.finite p)).1
  rw [P.V_mod_bijection_apply]
  simp [NumberFieldPlace.IsFinite, V_section,
    NumberFieldPlace.restrictionSection]

theorem selected_bad_place_comap
    (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod)
    (_hp : p ∈ P.V_mod_bad) :
    NumberFieldPlace.comap (k := A.Fmod)
        (P.V_mod_bijection (NumberFieldPlace.finite p)).1 =
      NumberFieldPlace.finite p := by
  rw [P.V_mod_bijection_apply]
  exact P.V_section.comap_lift (NumberFieldPlace.finite p)

theorem V_bad_nonempty
    (P : SourcePlaceSelection A) :
    (P.V_bad).Nonempty := by
  rcases P.V_mod_bad_nonempty with ⟨p, hp⟩
  exact ⟨P.V_mod_bijection (NumberFieldPlace.finite p),
    P.selected_bad_place_mem p hp⟩

theorem selected_place_is_finite_iff
    (P : SourcePlaceSelection A)
    (v : NumberFieldPlace A.Fmod) :
    NumberFieldPlace.IsFinite (P.V_mod_bijection v).1 =
      NumberFieldPlace.IsFinite (P.V_section.lift v) :=
  rfl

theorem selected_place_is_infinite_iff
    (P : SourcePlaceSelection A)
    (v : NumberFieldPlace A.Fmod) :
    NumberFieldPlace.IsInfinite (P.V_mod_bijection v).1 =
      NumberFieldPlace.IsInfinite (P.V_section.lift v) :=
  rfl

theorem selected_finite_places_nonempty
    (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    P.V_mod_bijection (NumberFieldPlace.finite p) ∈ P.V_non := by
  change NumberFieldPlace.IsFinite
    (P.V_mod_bijection (NumberFieldPlace.finite p)).1
  rw [P.V_mod_bijection_apply]
  simp [NumberFieldPlace.IsFinite, V_section,
    NumberFieldPlace.restrictionSection]

theorem selected_infinite_places_arc
    (P : SourcePlaceSelection A)
    (v : NumberField.InfinitePlace A.Fmod) :
    P.V_mod_bijection (NumberFieldPlace.infinite v) ∈ P.V_arc := by
  change NumberFieldPlace.IsInfinite
    (P.V_mod_bijection (NumberFieldPlace.infinite v)).1
  rw [P.V_mod_bijection_apply]
  simp [NumberFieldPlace.IsInfinite, V_section,
    NumberFieldPlace.restrictionSection]

/-!
  This theorem is the exact place-field projection needed by the source
  sign-quotient record.  It is intentionally a conjunction of the actual
  fields, so downstream constructors can use it without recreating choices.
-/
theorem source_place_fields
    (P : SourcePlaceSelection A) :
    (∃ s : NumberFieldPlace.RestrictionSection A.Fmod A.K,
      s.selected = P.V ∧
      (∀ v : {v : NumberFieldPlace A.K // v ∈ P.V},
        NumberFieldPlace.comap (k := A.Fmod) v.1 =
          P.V_mod_bijection.symm v)) := by
  refine ⟨P.V_section, ?_, ?_⟩
  · rfl
  · exact P.V_place_comap

end SourcePlaceSelection

end InitialThetaSource

end

end LeanFormal.IUT
