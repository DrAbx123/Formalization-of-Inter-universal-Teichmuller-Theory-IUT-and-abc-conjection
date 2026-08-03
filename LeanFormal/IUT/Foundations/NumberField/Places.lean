import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
  A disjoint finite/infinite place carrier for number fields.

  The constructors retain the actual Mathlib place objects. Restriction along
  a number-field extension preserves the finite/infinite kind and delegates
  to the standard contraction/composition maps. This is a lower carrier, not
  a set of selected IUT places.
-/

namespace LeanFormal.IUT

universe u v

inductive NumberFieldPlace (K : Type u) [Field K] [NumberField K] where
  | finite : NumberField.FinitePlace K → NumberFieldPlace K
  | infinite : NumberField.InfinitePlace K → NumberFieldPlace K

namespace NumberFieldPlace

variable {K : Type u} [Field K] [NumberField K]

def IsFinite : NumberFieldPlace K → Prop
  | finite _ => True
  | infinite _ => False

def IsInfinite : NumberFieldPlace K → Prop
  | finite _ => False
  | infinite _ => True

@[simp] theorem isFinite_finite (place : NumberField.FinitePlace K) :
    IsFinite (finite place) :=
  trivial

@[simp] theorem not_isFinite_infinite (place : NumberField.InfinitePlace K) :
    ¬ IsFinite (infinite place) :=
  id

@[simp] theorem isInfinite_infinite (place : NumberField.InfinitePlace K) :
    IsInfinite (infinite place) :=
  trivial

@[simp] theorem not_isInfinite_finite (place : NumberField.FinitePlace K) :
    ¬ IsInfinite (finite place) :=
  id

noncomputable def comap
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] :
    NumberFieldPlace K → NumberFieldPlace k
  | finite place => finite (NumberFieldFinitePlace.comap place)
  | infinite place => infinite (place.comap (algebraMap k K))

@[simp] theorem comap_finite
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (place : NumberField.FinitePlace K) :
    comap (k := k) (finite place) =
      finite (NumberFieldFinitePlace.comap place) :=
  rfl

@[simp] theorem comap_infinite
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (place : NumberField.InfinitePlace K) :
    comap (k := k) (infinite place) =
      infinite (place.comap (algebraMap k K)) :=
  rfl

@[simp] theorem comap_comap
    {k K L : Type*}
    [Field k] [NumberField k]
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L]
    (place : NumberFieldPlace L) :
    comap (k := k) (comap (k := K) place) = comap (k := k) place := by
  cases place with
  | finite place =>
      simp only [comap_finite]
      rw [NumberFieldFinitePlace.comap_comap]
  | infinite place =>
      simp only [comap_infinite]
      rw [← NumberField.InfinitePlace.comap_comp,
        IsScalarTower.algebraMap_eq k K L]

/-- A noncanonical extension of a finite place along a number-field extension. -/
noncomputable def finiteLift
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (place : NumberField.FinitePlace k) :
    NumberField.FinitePlace K :=
  Classical.choose
    (NumberFieldFinitePlace.comap_surjective (K := K) place)

@[simp] theorem comap_finiteLift
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (place : NumberField.FinitePlace k) :
    NumberFieldFinitePlace.comap (k := k) (finiteLift (K := K) place) =
      place :=
  Classical.choose_spec
    (NumberFieldFinitePlace.comap_surjective (K := K) place)

/-- A noncanonical extension of an infinite place along a number-field extension. -/
noncomputable def infiniteLift
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (place : NumberField.InfinitePlace k) :
    NumberField.InfinitePlace K :=
  Classical.choose
    (NumberField.InfinitePlace.comap_surjective (K := K) place)

@[simp] theorem comap_infiniteLift
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (place : NumberField.InfinitePlace k) :
    (infiniteLift (K := K) place).comap (algebraMap k K) = place :=
  Classical.choose_spec
    (NumberField.InfinitePlace.comap_surjective (K := K) place)

/-- A section of restriction on the full finite/infinite place carrier. -/
structure RestrictionSection
    (k : Type u) (K : Type v)
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] where
  lift : NumberFieldPlace k -> NumberFieldPlace K
  comap_lift : forall place, comap (k := k) (lift place) = place

/-- A place section obtained by choosing one extension of each place. -/
noncomputable def restrictionSection
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] :
    RestrictionSection k K where
  lift
    | finite place => finite (finiteLift (K := K) place)
    | infinite place => infinite (infiniteLift (K := K) place)
  comap_lift place := by
    cases place with
    | finite place =>
        simp only [comap_finite, comap_finiteLift]
    | infinite place =>
        simp only [comap_infinite, comap_infiniteLift]

namespace RestrictionSection

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K]
  [Algebra k K]

/-- The selected set of upstairs places, i.e. the image of a section. -/
def selected (selection : RestrictionSection k K) :
    Set (NumberFieldPlace K) :=
  Set.range selection.lift

theorem lift_injective (selection : RestrictionSection k K) :
    Function.Injective selection.lift :=
  Function.LeftInverse.injective selection.comap_lift

/-- Restriction identifies the selected image exactly with all lower places. -/
noncomputable def selectedEquiv (selection : RestrictionSection k K) :
    NumberFieldPlace k ≃
      {place : NumberFieldPlace K // place ∈ selection.selected} where
  toFun place :=
    ⟨selection.lift place, ⟨place, rfl⟩⟩
  invFun place := comap (k := k) place.1
  left_inv place := selection.comap_lift place
  right_inv place := by
    rcases place.property with ⟨lowerPlace, hplace⟩
    apply Subtype.ext
    change selection.lift (comap (k := k) place.1) = place.1
    rw [← hplace, selection.comap_lift]

@[simp] theorem selectedEquiv_apply
    (selection : RestrictionSection k K) (place : NumberFieldPlace k) :
    (selection.selectedEquiv place).1 = selection.lift place :=
  rfl

@[simp] theorem selectedEquiv_symm_apply
    (selection : RestrictionSection k K)
    (place : {place : NumberFieldPlace K // place ∈ selection.selected}) :
    selection.selectedEquiv.symm place = comap (k := k) place.1 :=
  rfl

end RestrictionSection

end NumberFieldPlace

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def numberFieldPlaces : Obligation :=
  { id := "Foundations.NumberField.places"
    source := "Standard finite and infinite places; IUT I initial-data prerequisites"
    status := VerificationStatus.proved
    note :=
      "A disjoint carrier retains Mathlib finite or infinite places. Lean " ++
        "proves the kind predicates, restriction formulas, and transitivity. " ++
        "Lying-over for finite places and extension of complex embeddings for " ++
        "infinite places produce a noncanonical restriction section; its " ++
        "selected image is proved equivalent to all lower places. No " ++
        "reduction condition or IUT link is supplied."
    dependsOn := ["Foundations.NumberField.finite-places"] }

end LeanFormal.IUT.Audit
