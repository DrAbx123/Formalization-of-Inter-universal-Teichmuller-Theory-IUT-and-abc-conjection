import LeanFormal.IUT.Audit.Status
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Ideal.GoingUp

/-!
  Finite places of number fields and their residue fields.

  Mathlib identifies a finite place with a height-one prime of the ring of
  integers.  This file exposes that identification, the resulting residue
  field and residue characteristic, and restriction along a number-field
  extension.  These are standard number-field constructions below the IUT
  initial-Theta-data layer.

  Source comparison: IUT I, Definition 3.1(b),(e); compare
  `promachina/iut-lean`, `Iut/Foundations/InitialThetaData.lean`, finite-place
  block.  The implementation here uses the current Mathlib 4.32.2
  `FinitePlace.maximalIdeal` API instead of choosing the ideal again.
-/

namespace LeanFormal.IUT

universe u v

namespace NumberFieldFinitePlace

variable {K : Type u} [Field K] [NumberField K]

noncomputable abbrev underlyingPrime (place : NumberField.FinitePlace K) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
  place.maximalIdeal

@[simp] theorem mk_underlyingPrime (place : NumberField.FinitePlace K) :
    NumberField.FinitePlace.mk (underlyingPrime place) = place := by
  exact NumberField.FinitePlace.mk_maximalIdeal place

abbrev ResidueField (place : NumberField.FinitePlace K) :=
  NumberField.RingOfIntegers K ⧸ (underlyingPrime place).asIdeal

noncomputable def residueCharacteristic
    (place : NumberField.FinitePlace K) : Nat :=
  ringChar (ResidueField place)

noncomputable instance residueFieldFinite
    (place : NumberField.FinitePlace K) :
    Finite (ResidueField place) := by
  exact place.maximalIdeal.asIdeal.finiteQuotientOfFreeOfNeBot
    place.maximalIdeal.ne_bot

theorem residueCharacteristic_prime
    (place : NumberField.FinitePlace K) :
    Nat.Prime (residueCharacteristic place) := by
  exact CharP.prime_ringChar (ResidueField place)

theorem residueCharacteristic_pos
    (place : NumberField.FinitePlace K) :
    0 < residueCharacteristic place :=
  (residueCharacteristic_prime place).pos

/- Restriction is induced by contraction of the height-one prime in the
larger ring of integers. -/
noncomputable def comap
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (place : NumberField.FinitePlace K) :
    NumberField.FinitePlace k :=
  NumberField.FinitePlace.mk
    { asIdeal :=
        place.maximalIdeal.asIdeal.comap
          (algebraMap (NumberField.RingOfIntegers k)
            (NumberField.RingOfIntegers K))
      isPrime := place.maximalIdeal.asIdeal.comap_isPrime _
      ne_bot :=
        Ideal.IsIntegral.comap_ne_bot
          (NumberField.RingOfIntegers k)
          place.maximalIdeal.ne_bot }

@[simp] theorem comap_maximalIdeal
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (place : NumberField.FinitePlace K) :
    (comap (k := k) place).maximalIdeal.asIdeal =
      place.maximalIdeal.asIdeal.comap
        (algebraMap (NumberField.RingOfIntegers k)
          (NumberField.RingOfIntegers K)) := by
  unfold comap
  rw [NumberField.FinitePlace.maximalIdeal_mk]

@[simp] theorem comap_comap
    {k K L : Type*}
    [Field k] [NumberField k]
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L]
    (place : NumberField.FinitePlace L) :
    comap (k := k) (comap (k := K) place) = comap (k := k) place := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  simp only [comap_maximalIdeal]
  rw [Ideal.comap_comap]
  congr 1
  ext x
  change
    (NumberField.RingOfIntegers.mapRingHom (algebraMap K L)
        (NumberField.RingOfIntegers.mapRingHom (algebraMap k K) x) : L) =
      NumberField.RingOfIntegers.mapRingHom (algebraMap k L) x
  simp only [NumberField.RingOfIntegers.mapRingHom_apply]
  exact (IsScalarTower.algebraMap_apply k K L (x : k)).symm

/-- Every finite place of a number field extends to a finite place upstairs. -/
theorem comap_surjective
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] :
    Function.Surjective
      (comap (k := k) : NumberField.FinitePlace K ->
        NumberField.FinitePlace k) := by
  intro place
  let P : Ideal (NumberField.RingOfIntegers k) :=
    place.maximalIdeal.asIdeal
  letI : P.IsMaximal := place.maximalIdeal.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := NumberField.RingOfIntegers K) P
  let primeQ :
      IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers K) :=
    { asIdeal := Q
      isPrime := hQmax.isPrime
      ne_bot :=
        Ring.ne_bot_of_isMaximal_of_not_isField hQmax
          (NumberField.RingOfIntegers.not_isField K) }
  refine ⟨NumberField.FinitePlace.mk primeQ, ?_⟩
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  simp only [comap_maximalIdeal,
    NumberField.FinitePlace.maximalIdeal_mk]
  exact ((Ideal.liesOver_iff Q P).mp hQover).symm

end NumberFieldFinitePlace

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def numberFieldFinitePlaces : Obligation :=
  { id := "Foundations.NumberField.finite-places"
    source := "Standard number-field finite places; IUT I, Definition 3.1(b),(e) prerequisites"
    status := VerificationStatus.proved
    note :=
      "Finite places use Mathlib's height-one prime equivalence. Residue " ++
        "fields and residue characteristics are defined from the canonical " ++
        "maximal ideal; restriction is constructed by ideal contraction and " ++
        "proved transitive in field towers. No elliptic reduction or IUT " ++
        "initial-data existence is asserted."
    dependsOn := [] }

end LeanFormal.IUT.Audit
