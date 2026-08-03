import Iut.Foundations.KummerFaithfulness
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Integral-unit and `G_m` Kummer rigidity for local fields

The integral-unit theorem is the exact arithmetic input used by the current
`M_TM^×` Kummer embedding.  It is not, by itself, the multiplicative case of
Absolute Anabelian Geometry III, Definition 1.5: even `G_m` has the full field
unit group as its rational points.  This file separately proves that full
`G_m` case over every finite local-field extension by controlling the discrete
valuation first.  Arbitrary tori and arbitrary semi-abelian varieties remain
the explicit obligations represented by the predicates in
`KummerFaithfulness.lean`.
-/

namespace Iut

namespace SourceMLFKummerFaithfulness

universe u

open ValuativeRel

set_option maxHeartbeats 800000 in
-- The quotient-module finiteness synthesis traverses the scalar tower.
/-- A finite algebra modulo an extended finite-index ideal is finite. -/
theorem finite_quotient_map
    (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S]
    (I : Ideal R) [Finite (R ⧸ I)] :
    Finite (S ⧸ I.map (algebraMap R S)) := by
  let J := I.map (algebraMap R S)
  let B := R ⧸ J.comap (algebraMap R S)
  let T := S ⧸ J
  let factor : R ⧸ I →+* B :=
    Ideal.Quotient.factor Ideal.le_comap_map
  letI : Finite B :=
    Finite.of_surjective factor
      (Ideal.Quotient.factor_surjective _)
  letI : Algebra B T := inferInstance
  letI : IsScalarTower R B T :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      rw [Algebra.smul_def, Algebra.smul_def]
      congr 1
  letI : Module.Finite R T := Module.Finite.quotient R J
  letI : Module.Finite B T :=
    Module.Finite.of_restrictScalars_finite R B T
  exact Module.finite_of_finite B

set_option maxHeartbeats 800000 in
-- Krull intersection and the quotient construction require deep synthesis.
/--
Finite quotients modulo powers of one proper ideal make the units of a finite
algebra residually finite.  Krull intersection supplies the separating power.
-/
theorem units_residuallyFinite_of_finite_quotients
    (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Finite R S]
    [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≠ ⊤)
    (finiteQuotient : ∀ n : ℕ, Finite (R ⧸ I ^ n)) :
    _root_.Group.ResiduallyFinite Sˣ := by
  apply _root_.Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro unit unit_ne_one
  have value_sub_one_ne_zero : (unit : S) - 1 ≠ 0 := by
    intro equality
    apply unit_ne_one
    apply Units.ext
    exact sub_eq_zero.mp equality
  have exists_separating_power :
      ∃ n : ℕ,
        (unit : S) - 1 ∉
          (I ^ n • (⊤ : Submodule R S)) := by
    by_contra no_power
    push Not at no_power
    have in_intersection :
        (unit : S) - 1 ∈
          (⨅ n : ℕ, I ^ n • (⊤ : Submodule R S)) :=
      (Submodule.mem_iInf _).mpr no_power
    rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing I hI]
      at in_intersection
    exact value_sub_one_ne_zero
      ((Submodule.mem_bot R).mp in_intersection)
  obtain ⟨n, separating⟩ := exists_separating_power
  let J : Ideal S := (I ^ n).map (algebraMap R S)
  have separating_ideal : (unit : S) - 1 ∉ J := by
    intro member
    apply separating
    rw [Ideal.smul_top_eq_map]
    exact member
  letI : Finite (R ⧸ I ^ n) := finiteQuotient n
  letI : Finite (S ⧸ J) := finite_quotient_map R S (I ^ n)
  let reduction : Sˣ →* (S ⧸ J)ˣ :=
    Units.map (Ideal.Quotient.mk J)
  refine ⟨(S ⧸ J)ˣ, inferInstance, inferInstance, reduction, ?_⟩
  intro reduction_eq_one
  apply separating_ideal
  apply (Ideal.Quotient.mk_eq_one_iff_sub_mem (unit : S)).mp
  exact congrArg Units.val reduction_eq_one

variable
  (K : Type u) [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The unit group of the valuation ring of an MLF is profinite. -/
noncomputable def valuationRingUnitsProfinite : Profinite :=
  by
    letI := IsTopologicalAddGroup.rightUniformSpace K
    letI := isUniformAddGroup_of_addCommGroup (G := K)
    letI : Valued K (ValueGroupWithZero K) := inferInstance
    letI : (Valued.v (R := K)).RankOne :=
      { hom' :=
          IsRankLeOne.nonempty.some.emb (R := K).comp
            MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' :=
          IsRankLeOne.nonempty.some.strictMono.comp
            MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    let R := Valuation.integer (valuation K)
    open scoped Valued in
      letI : NontriviallyNormedField K := inferInstance
      letI : IsUltrametricDist K := inferInstance
      letI : TotallyDisconnectedSpace K := inferInstance
      letI : T1Space R := inferInstance
      letI : TotallyDisconnectedSpace R := inferInstance
      letI : TotallyDisconnectedSpace Rᵐᵒᵖ :=
        MulOpposite.opHomeomorph.totallyDisconnectedSpace
      letI : TotallyDisconnectedSpace Rˣ :=
        (Units.isEmbedding_embedProduct.isTotallyDisconnected_range).mp
          (isTotallyDisconnected_of_totallyDisconnectedSpace _)
      exact Profinite.of Rˣ

/-- A valuation-ring unit admitting roots of every positive degree within the
valuation-ring unit group is trivial. -/
theorem valuationRingUnit_eq_one_of_roots
    (value : (Valuation.integer (valuation K))ˣ)
    (roots : ∀ n : ℕ, 0 < n →
      ∃ root : (Valuation.integer (valuation K))ˣ,
        root ^ n = value) :
    value = 1 := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  letI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : Valued K (ValueGroupWithZero K) := inferInstance
  letI : (Valued.v (R := K)).RankOne :=
    { hom' :=
        IsRankLeOne.nonempty.some.emb (R := K).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' :=
        IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let R := Valuation.integer (valuation K)
  open scoped Valued in
    letI : NontriviallyNormedField K := inferInstance
    letI : IsUltrametricDist K := inferInstance
    letI : TotallyDisconnectedSpace K := inferInstance
    letI : T1Space R := inferInstance
    letI : TotallyDisconnectedSpace R := inferInstance
    letI : TotallyDisconnectedSpace Rᵐᵒᵖ :=
      MulOpposite.opHomeomorph.totallyDisconnectedSpace
    letI : TotallyDisconnectedSpace Rˣ :=
      (Units.isEmbedding_embedProduct.isTotallyDisconnected_range).mp
        (isTotallyDisconnected_of_totallyDisconnectedSpace _)
    exact
      SourceKummerFaithfulness.eq_one_of_roots_in_profinite value roots

set_option maxHeartbeats 800000 in
-- Integral-closure finiteness and DVR quotient instances synthesize together.
/--
The integral units in every finite extension of an MLF are residually finite.
This is the finite-base-change input used by the integral-unit Kummer map; it
does not include the valuation factor of the full multiplicative group.
-/
theorem integralClosureUnits_residuallyFinite
    [CharZero K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] :
    _root_.Group.ResiduallyFinite
      (integralClosure
        (Valuation.integer (valuation K)) L)ˣ := by
  let R := Valuation.integer (valuation K)
  let S := integralClosure R L
  letI : IsFractionRing R K := inferInstance
  letI : Module.Finite R S :=
    IsIntegralClosure.finite R K L S
  apply units_residuallyFinite_of_finite_quotients
    R S (IsLocalRing.maximalIdeal R)
  · exact Ideal.IsPrime.ne_top'
  · intro n
    letI := IsTopologicalAddGroup.rightUniformSpace K
    letI := isUniformAddGroup_of_addCommGroup (G := K)
    letI : Valued K (ValueGroupWithZero K) := inferInstance
    letI : IsDiscreteValuationRing (Valued.integer K) := by
      change IsDiscreteValuationRing R
      infer_instance
    letI : Finite (Valued.ResidueField K) := by
      change Finite (IsLocalRing.ResidueField R)
      infer_instance
    exact
      Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField
        (K := K) inferInstance n

private theorem multiplicativeInt_eq_one_of_roots
    (value : Multiplicative ℤ)
    (roots : ∀ n : ℕ, 0 < n →
      ∃ root : Multiplicative ℤ, root ^ n = value) :
    value = 1 := by
  let n := value.toAdd.natAbs + 1
  obtain ⟨root, root_pow⟩ := roots n (Nat.succ_pos _)
  have multiple : (n : ℤ) * root.toAdd = value.toAdd := by
    simpa [nsmul_eq_mul] using congrArg Multiplicative.toAdd root_pow
  have dvd : (n : ℤ) ∣ value.toAdd :=
    ⟨root.toAdd, multiple.symm⟩
  have abs_lt : |value.toAdd| < (n : ℤ) := by
    dsimp [n]
    rw [← Int.natCast_natAbs]
    exact_mod_cast Nat.lt_succ_self value.toAdd.natAbs
  have value_zero := Int.eq_zero_of_abs_lt_dvd dvd abs_lt
  change value.toAdd = (1 : Multiplicative ℤ).toAdd
  simpa using value_zero

private noncomputable def localFieldUnitValuation
    (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    Fˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    ((Units.map
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toMonoidWithZeroHom.toMonoidHom).comp
      (Units.map (valuation F).toMonoidWithZeroHom.toMonoidHom))

private theorem localFieldUnitValuation_eq_one_iff
    (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (value : Fˣ) :
    localFieldUnitValuation F value = 1 ↔
      valuation F (value : F) = 1 := by
  let valueGroupValue : (ValueGroupWithZero F)ˣ :=
    Units.map (valuation F).toMonoidWithZeroHom.toMonoidHom value
  let integerValue : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toMonoidWithZeroHom.toMonoidHom
      valueGroupValue
  change WithZero.unitsWithZeroEquiv integerValue = 1 ↔ _
  constructor
  · intro h
    have integerValue_eq_one : integerValue = 1 :=
      WithZero.unitsWithZeroEquiv.injective (by simpa using h)
    have valueGroupValue_eq_one : valueGroupValue = 1 := by
      apply (Units.map_injective
        (f :=
          (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toMonoidWithZeroHom.toMonoidHom)
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).injective)
      simpa only [integerValue, map_one] using integerValue_eq_one
    exact congrArg Units.val valueGroupValue_eq_one
  · intro h
    have valueGroupValue_eq_one : valueGroupValue = 1 := by
      apply Units.ext
      exact h
    have integerValue_eq_one : integerValue = 1 := by
      change Units.map _ valueGroupValue = 1
      rw [valueGroupValue_eq_one, map_one]
    simpa only [map_one] using
      congrArg WithZero.unitsWithZeroEquiv integerValue_eq_one

private theorem localFieldUnitValuation_eq_one_of_roots
    (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (value : Fˣ)
    (roots : ∀ n : ℕ, 0 < n → ∃ root : Fˣ, root ^ n = value) :
    localFieldUnitValuation F value = 1 := by
  apply multiplicativeInt_eq_one_of_roots
  intro n hn
  obtain ⟨root, root_pow⟩ := roots n hn
  refine ⟨localFieldUnitValuation F root, ?_⟩
  rw [← map_pow, root_pow]

private noncomputable def valuationRingUnitOfFieldUnit
    (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (value : Fˣ)
    (valuation_eq_one : valuation F (value : F) = 1) :
    (Valuation.integer (valuation F))ˣ where
  val := ⟨value, valuation_eq_one.le⟩
  inv := ⟨(value : F)⁻¹, by
    rw [Valuation.mem_integer_iff]
    change valuation F ((value : F)⁻¹) ≤ 1
    rw [map_inv₀, valuation_eq_one, inv_one]⟩
  val_inv := by
    apply Subtype.ext
    exact mul_inv_cancel₀ value.ne_zero
  inv_val := by
    apply Subtype.ext
    exact inv_mul_cancel₀ value.ne_zero

@[simp]
private theorem valuationRingUnitOfFieldUnit_val
    (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (value : Fˣ)
    (valuation_eq_one : valuation F (value : F) = 1) :
    ((valuationRingUnitOfFieldUnit F value valuation_eq_one :
        Valuation.integer (valuation F)) : F) = value :=
  rfl

/-- The full multiplicative group of a nonarchimedean local field has no
nontrivial element admitting roots of every positive degree.  The valuation
must vanish, after which the integral-unit theorem applies. -/
theorem fieldUnit_eq_one_of_roots
    (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (value : Fˣ)
    (roots : ∀ n : ℕ, 0 < n → ∃ root : Fˣ, root ^ n = value) :
    value = 1 := by
  have value_valuation_eq_one : valuation F (value : F) = 1 :=
    (localFieldUnitValuation_eq_one_iff F value).mp
      (localFieldUnitValuation_eq_one_of_roots F value roots)
  let integralValue :=
    valuationRingUnitOfFieldUnit F value value_valuation_eq_one
  have integralRoots :
      ∀ n : ℕ, 0 < n →
        ∃ root : (Valuation.integer (valuation F))ˣ,
          root ^ n = integralValue := by
    intro n hn
    obtain ⟨root, root_pow⟩ := roots n hn
    have root_valuation_hom_pow :
        (localFieldUnitValuation F root) ^ n = 1 := by
      rw [← map_pow, root_pow,
        localFieldUnitValuation_eq_one_of_roots F value roots]
    have root_valuation_hom_eq_one :
        localFieldUnitValuation F root = 1 :=
      (pow_eq_one_iff_left hn.ne').mp root_valuation_hom_pow
    have root_valuation_eq_one :
        valuation F (root : F) = 1 :=
      (localFieldUnitValuation_eq_one_iff F root).mp
        root_valuation_hom_eq_one
    let integralRoot :=
      valuationRingUnitOfFieldUnit F root root_valuation_eq_one
    refine ⟨integralRoot, ?_⟩
    apply Units.ext
    apply Subtype.ext
    exact congrArg Units.val root_pow
  have integralValue_eq_one : integralValue = 1 :=
    valuationRingUnit_eq_one_of_roots F integralValue integralRoots
  apply Units.ext
  have equality := congrArg
    (fun unit : (Valuation.integer (valuation F))ˣ =>
      (((unit : Valuation.integer (valuation F)) : F)))
    integralValue_eq_one
  simpa [integralValue] using equality

/-- The `G_m` clause on `Lˣ` for an arbitrary finite local-field extension
`L/K`.  The extra local-field instances name the canonical valuation and
topology on `L`; no integral-unit restriction remains in the conclusion. -/
theorem finiteExtensionGMUnit_eq_one_of_roots
    (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : _root_.Iut.SourceKummerFaithfulness.FiniteExtension K)
    [ValuativeRel L.carrier] [TopologicalSpace L.carrier]
    [IsNonarchimedeanLocalField L.carrier]
    (value : L.carrierˣ)
    (roots :
      ∀ n : ℕ, 0 < n → ∃ root : L.carrierˣ, root ^ n = value) :
    value = 1 :=
  fieldUnit_eq_one_of_roots L.carrier value roots

/-- Injectivity of a `G_m` Kummer map over every finite local-field extension
is derived from its standard kernel characterization and the preceding
root-rigidity theorem; injectivity is not a field of the map presentation. -/
theorem finiteExtensionGMKummerMap_injective
    (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : _root_.Iut.SourceKummerFaithfulness.FiniteExtension K)
    [ValuativeRel L.carrier] [TopologicalSpace L.carrier]
    [IsNonarchimedeanLocalField L.carrier]
    {C : Type u} [CommGroup C]
    (kummerMap :
      _root_.Iut.SourceKummerFaithfulness.MultiplicativeKummerMap
        L.carrierˣ C) :
    Function.Injective kummerMap.hom :=
  kummerMap.injective_of_roots_eq_one
    (finiteExtensionGMUnit_eq_one_of_roots K L)

end SourceMLFKummerFaithfulness

end Iut
