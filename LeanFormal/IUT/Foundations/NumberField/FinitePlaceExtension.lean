import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
  Extension of finite places, valuations, and local completions.

  If an upstairs finite place is restricted by ideal contraction, its maximal
  ideal lies over the lower maximal ideal. Mathlib's ramification theorem then
  compares the two discrete valuations and proves the field embedding
  uniformly continuous. This file extends that embedding to a ring homomorphism
  between the corresponding adic completions.
-/

namespace LeanFormal.IUT

universe u v

namespace NumberFieldFinitePlace

noncomputable section

open WithZeroTopology

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K]
  [Algebra k K]

instance comap_liesOver (place : NumberField.FinitePlace K) :
    place.maximalIdeal.asIdeal.LiesOver
      (comap (k := k) place).maximalIdeal.asIdeal := by
  exact (Ideal.liesOver_iff _ _).mpr (comap_maximalIdeal place)

/-- Valuations along a place extension differ by the ramification index. -/
theorem valuation_algebraMap
    (place : NumberField.FinitePlace K) (x : k) :
    (comap (k := k) place).maximalIdeal.valuation k x ^
        (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
          place.maximalIdeal.asIdeal =
      place.maximalIdeal.valuation K (algebraMap k K x) := by
  exact
    IsDedekindDomain.HeightOneSpectrum.valuation_liesOver
      K (comap (k := k) place).maximalIdeal place.maximalIdeal x

/-- The valued field embedding is uniformly continuous at a place above. -/
theorem uniformContinuous_algebraMap
    (place : NumberField.FinitePlace K) :
    UniformContinuous
      (algebraMap
        (WithVal ((comap (k := k) place).maximalIdeal.valuation k))
        (WithVal (place.maximalIdeal.valuation K))) := by
  exact
    IsDedekindDomain.HeightOneSpectrum.uniformContinuous_algebraMap_liesOver
      (K := k) K (comap (k := k) place).maximalIdeal place.maximalIdeal

/-- The extension `k_v -> K_w` on actual adic completions. -/
def completionMap (place : NumberField.FinitePlace K) :
    (comap (k := k) place).maximalIdeal.adicCompletion k →+*
      place.maximalIdeal.adicCompletion K :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv
      K place.maximalIdeal).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom
        (algebraMap
          (WithVal ((comap (k := k) place).maximalIdeal.valuation k))
          (WithVal (place.maximalIdeal.valuation K)))
        (uniformContinuous_algebraMap place).continuous).comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.equiv
        k (comap (k := k) place).maximalIdeal).toRingHom)

/-- The extension between the two local fields is continuous. -/
theorem continuous_completionMap
    (place : NumberField.FinitePlace K) :
    Continuous (completionMap (k := k) place) :=
  (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_ofCompletion
      K place.maximalIdeal).comp <|
    UniformSpace.Completion.continuous_map.comp
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion.continuous_toCompletion
        k (comap (k := k) place).maximalIdeal)

/-- A finite-place extension embeds the lower local field into the upper one. -/
theorem completionMap_injective
    (place : NumberField.FinitePlace K) :
    Function.Injective (completionMap (k := k) place) :=
  RingHom.injective _

/-- On the dense base field, the completion map is the original algebra map. -/
theorem completionMap_coe
    (place : NumberField.FinitePlace K) (x : k) :
    completionMap place
        (x : (comap (k := k) place).maximalIdeal.adicCompletion k) =
      (algebraMap k K x : place.maximalIdeal.adicCompletion K) := by
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  change
    UniformSpace.Completion.map
        (algebraMap
          (WithVal ((comap (k := k) place).maximalIdeal.valuation k))
          (WithVal (place.maximalIdeal.valuation K)))
        (↑(WithVal.toVal
          ((comap (k := k) place).maximalIdeal.valuation k) x)) =
      ↑(WithVal.toVal (place.maximalIdeal.valuation K)
        (algebraMap k K x))
  rw [UniformSpace.Completion.map_coe
    (uniformContinuous_algebraMap place)]
  rfl

/-- The ramification formula extends from the dense global field to every
element of the lower local field. -/
theorem valuation_completionMap
    (place : NumberField.FinitePlace K)
    (x : (comap (k := k) place).maximalIdeal.adicCompletion k) :
    Valued.v x ^
        (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
          place.maximalIdeal.asIdeal =
      Valued.v (completionMap (k := k) place x) := by
  have lowerSurjective :
      Function.Surjective
        (Valued.v :
          (comap (k := k) place).maximalIdeal.adicCompletion k ->
            WithZero (Multiplicative ℤ)) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
      k (comap (k := k) place).maximalIdeal
  have upperSurjective :
      Function.Surjective
        (Valued.v : place.maximalIdeal.adicCompletion K ->
          WithZero (Multiplicative ℤ)) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
      K place.maximalIdeal
  have leftContinuous :
      Continuous (fun y :
          (comap (k := k) place).maximalIdeal.adicCompletion k =>
        Valued.v y ^
          (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
            place.maximalIdeal.asIdeal) :=
    (Valued.continuous_valuation_of_surjective lowerSurjective).pow _
  have rightContinuous :
      Continuous (fun y :
          (comap (k := k) place).maximalIdeal.adicCompletion k =>
        Valued.v (completionMap (k := k) place y)) :=
    (Valued.continuous_valuation_of_surjective upperSurjective).comp
      (continuous_completionMap (k := k) place)
  have agreeOnBase :
      (fun y : (comap (k := k) place).maximalIdeal.adicCompletion k =>
          Valued.v y ^
            (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
              place.maximalIdeal.asIdeal) ∘
          algebraMap k
            ((comap (k := k) place).maximalIdeal.adicCompletion k) =
        (fun y : (comap (k := k) place).maximalIdeal.adicCompletion k =>
          Valued.v (completionMap (k := k) place y)) ∘
          algebraMap k
            ((comap (k := k) place).maximalIdeal.adicCompletion k) := by
    funext y
    simp only [Function.comp_apply]
    change
      Valued.v
          (y : (comap (k := k) place).maximalIdeal.adicCompletion k) ^
            (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
              place.maximalIdeal.asIdeal =
        Valued.v
          (completionMap (k := k) place
            (y : (comap (k := k) place).maximalIdeal.adicCompletion k))
    rw [completionMap_coe,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact valuation_algebraMap place y
  exact congrFun
    ((IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
        (K := k)
        (v := (comap (k := k) place).maximalIdeal)).equalizer
      leftContinuous rightContinuous agreeOnBase) x

/-- The local-field embedding sends the lower valuation ring into the upper
valuation ring. -/
theorem completionMap_mem_adicCompletionIntegers
    (place : NumberField.FinitePlace K)
    {x : (comap (k := k) place).maximalIdeal.adicCompletion k}
    (hx : x ∈
      (comap (k := k) place).maximalIdeal.adicCompletionIntegers k) :
    completionMap (k := k) place x ∈
      place.maximalIdeal.adicCompletionIntegers K := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rw [← valuation_completionMap]
  exact pow_le_one₀ bot_le hx

/-- The induced homomorphism between the two completed valuation rings. -/
def completionIntegersMap (place : NumberField.FinitePlace K) :
    (comap (k := k) place).maximalIdeal.adicCompletionIntegers k →+*
      place.maximalIdeal.adicCompletionIntegers K :=
  RingHom.codRestrict
    ((completionMap (k := k) place).comp
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k).subtype)
    (place.maximalIdeal.adicCompletionIntegers K)
    (fun x => completionMap_mem_adicCompletionIntegers place x.property)

@[simp]
theorem coe_completionIntegersMap
    (place : NumberField.FinitePlace K)
    (x : (comap (k := k) place).maximalIdeal.adicCompletionIntegers k) :
    ((completionIntegersMap (k := k) place x :
        place.maximalIdeal.adicCompletionIntegers K) :
      place.maximalIdeal.adicCompletion K) =
      completionMap (k := k) place
        (x : (comap (k := k) place).maximalIdeal.adicCompletion k) :=
  rfl

/-- The valuation-ring homomorphism remains injective. -/
theorem completionIntegersMap_injective
    (place : NumberField.FinitePlace K) :
    Function.Injective (completionIntegersMap (k := k) place) := by
  intro x y hxy
  apply Subtype.ext
  exact completionMap_injective place (congrArg Subtype.val hxy)

/-- The local-field and valuation-ring embeddings form the expected square. -/
theorem completionMap_comp_algebraMap
    (place : NumberField.FinitePlace K) :
    (completionMap (k := k) place).comp
        (algebraMap
          ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
          ((comap (k := k) place).maximalIdeal.adicCompletion k)) =
      (algebraMap
        (place.maximalIdeal.adicCompletionIntegers K)
        (place.maximalIdeal.adicCompletion K)).comp
          (completionIntegersMap (k := k) place) := by
  apply RingHom.ext
  intro x
  change completionMap (k := k) place
      (x : (comap (k := k) place).maximalIdeal.adicCompletion k) =
    ((completionIntegersMap (k := k) place x :
        place.maximalIdeal.adicCompletionIntegers K) :
      place.maximalIdeal.adicCompletion K)
  exact (coe_completionIntegersMap (k := k) place x).symm

/-- The ramification index at an upper finite place is positive. -/
theorem ramificationIdx_ne_zero
    (place : NumberField.FinitePlace K) :
    (comap (k := k) place).maximalIdeal.asIdeal.ramificationIdx'
        place.maximalIdeal.asIdeal ≠ 0 :=
  Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
    place.maximalIdeal.asIdeal
    (comap (k := k) place).maximalIdeal.ne_bot

/-- The map on completed valuation rings is a local homomorphism. -/
theorem isLocalHom_completionIntegersMap
    (place : NumberField.FinitePlace K) :
    IsLocalHom (completionIntegersMap (k := k) place) where
  map_nonunit x hx := by
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      at hx ⊢
    rw [coe_completionIntegersMap, ← valuation_completionMap] at hx
    exact (pow_eq_one_iff_of_nonneg bot_le (ramificationIdx_ne_zero place)).mp hx

/-- The embedding of residue fields induced by a finite-place extension. -/
noncomputable def residueMap (place : NumberField.FinitePlace K) :
    IsLocalRing.ResidueField
        ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) →+*
      IsLocalRing.ResidueField
        (place.maximalIdeal.adicCompletionIntegers K) := by
  letI : IsLocalHom (completionIntegersMap (k := k) place) :=
    isLocalHom_completionIntegersMap place
  exact IsLocalRing.ResidueField.map (completionIntegersMap (k := k) place)

/-- Reduction commutes with the map on completed valuation rings. -/
@[simp]
theorem residueMap_residue
    (place : NumberField.FinitePlace K)
    (x : (comap (k := k) place).maximalIdeal.adicCompletionIntegers k) :
    residueMap (k := k) place
        (IsLocalRing.residue
          ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) x) =
      IsLocalRing.residue
        (place.maximalIdeal.adicCompletionIntegers K)
        (completionIntegersMap (k := k) place x) := by
  letI : IsLocalHom (completionIntegersMap (k := k) place) :=
    isLocalHom_completionIntegersMap place
  exact IsLocalRing.ResidueField.map_residue
    (completionIntegersMap (k := k) place) x

/-- The induced map on residue fields is injective. -/
theorem residueMap_injective
    (place : NumberField.FinitePlace K) :
    Function.Injective (residueMap (k := k) place) :=
  RingHom.injective _

end


end NumberFieldFinitePlace

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def finitePlaceExtension : Obligation :=
  { id := "Foundations.NumberField.finite-place-extension"
    source := "Standard ramification theory for number-field finite places"
    status := VerificationStatus.proved
    note :=
      "An upstairs finite place is proved to lie over its contraction. The " ++
        "valuation ramification-index formula and uniform continuity of the " ++
        "valued field embedding are inherited from Mathlib, and the induced " ++
        "continuous injective ring homomorphism between adic completions is " ++
        "constructed with its base-field formula proved. The ramification " ++
        "valuation formula is then extended to every element of the lower " ++
        "completion by continuity and density, and an injective homomorphism " ++
        "between the corresponding valuation rings is obtained. This map is " ++
        "local and induces an injective map of residue fields."
    dependsOn := ["Foundations.NumberField.finite-places"] }

end LeanFormal.IUT.Audit
