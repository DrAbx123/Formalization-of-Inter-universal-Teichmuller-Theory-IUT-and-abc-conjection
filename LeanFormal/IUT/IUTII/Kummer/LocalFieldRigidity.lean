/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.TimesMuIsm
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

namespace LeanFormal.IUT

/-!
  Multiplicative Kummer rigidity for a nonarchimedean local field.

  This is the `G_m` kernel needed before constructing the unit Kummer
  isomorphism.  The proof is adapted from `promachina/iut-lean`,
  `KummerFaithfulness.lean` and `SourceMLFKummerFaithfulness.lean`, upstream
  commit `3de1d7c1`, under Apache-2.0.  It deliberately does not state the
  stronger arbitrary-torus or semi-abelian Kummer-faithfulness predicates.
-/

universe u

namespace LocalFieldKummerRigidity

def HasAllPositiveRoots {A : Type u} [Group A] (value : A) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ root : A, root ^ n = value

structure MultiplicativeKummerMap
    (A C : Type u) [CommGroup A] [CommGroup C] where
  hom : A →* C
  map_eq_one_iff_roots : ∀ value : A, hom value = 1 ↔ HasAllPositiveRoots value

theorem MultiplicativeKummerMap.injective_of_roots_eq_one
    {A C : Type u} [CommGroup A] [CommGroup C]
    (kummerMap : MultiplicativeKummerMap A C)
    (rootRigidity : ∀ value : A, HasAllPositiveRoots value → value = 1) :
    Function.Injective kummerMap.hom := by
  intro first second hequal
  have quotient_map_eq_one : kummerMap.hom (first * second⁻¹) = 1 := by
    rw [map_mul, map_inv, hequal, mul_inv_cancel]
  have quotient_eq_one : first * second⁻¹ = 1 :=
    rootRigidity (first * second⁻¹)
      ((kummerMap.map_eq_one_iff_roots _).mp quotient_map_eq_one)
  exact eq_of_mul_inv_eq_one quotient_eq_one

theorem eq_one_of_roots_of_residuallyFinite
    {A : Type u} [Group A] [Group.ResiduallyFinite A]
    (value : A) (roots : HasAllPositiveRoots value) : value = 1 := by
  apply Group.eq_one_iff_forall_finiteIndexNormalSubroup value
  intro H
  let quotient := A ⧸ H.toSubgroup
  have quotientFinite : Finite quotient := inferInstance
  obtain ⟨root, hroot⟩ := roots (Nat.card quotient) Nat.card_pos
  change value ∈ H.toSubgroup
  rw [← QuotientGroup.eq_one_iff]
  rw [← hroot, QuotientGroup.mk_pow]
  exact pow_card_eq_one'

theorem residuallyFinite_of_profinite
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [TotallyDisconnectedSpace A] :
    Group.ResiduallyFinite A := by
  apply Group.residuallyFinite_iff_exists_finiteIndexNormalSubgroup.mpr
  intro x hx
  obtain ⟨H, hH⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (isClosed_singleton.isOpen_compl : IsOpen ({x}ᶜ : Set A))
      (by simpa [eq_comm] using hx)
  exact
    ⟨H.toFiniteIndexNormalSubgroup,
      fun hmem ↦ (hH hmem) rfl⟩

theorem eq_one_of_roots_in_profinite
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [TotallyDisconnectedSpace A]
    (value : A) (roots : HasAllPositiveRoots value) : value = 1 := by
  letI : Group.ResiduallyFinite A := residuallyFinite_of_profinite
  exact eq_one_of_roots_of_residuallyFinite value roots

open ValuativeRel

variable (K : Type u) [Field K] [ValuativeRel K]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

noncomputable def valuationRingUnitsProfinite : Profinite := by
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

theorem valuationRingUnit_eq_one_of_roots
    (value : (Valuation.integer (valuation K))ˣ)
    (roots : HasAllPositiveRoots value) : value = 1 := by
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
    exact eq_one_of_roots_in_profinite value roots

private theorem multiplicativeInt_eq_one_of_roots
    (value : Multiplicative ℤ) (roots : HasAllPositiveRoots value) : value = 1 := by
  let n := value.toAdd.natAbs + 1
  obtain ⟨root, root_pow⟩ := roots n (Nat.succ_pos _)
  have multiple : (n : ℤ) * root.toAdd = value.toAdd := by
    simpa [nsmul_eq_mul] using congrArg Multiplicative.toAdd root_pow
  have dvd : (n : ℤ) ∣ value.toAdd := ⟨root.toAdd, multiple.symm⟩
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
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (value : Fˣ) :
    localFieldUnitValuation F value = 1 ↔ valuation F (value : F) = 1 := by
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
      WithZero.unitsWithZeroEquiv.injective (by simpa only [map_one] using h)
    have valueGroupValue_eq_one : valueGroupValue = 1 := by
      apply (Units.map_injective
        (f :=
          (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toMonoidWithZeroHom.toMonoidHom)
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).injective
      )
      simpa only [integerValue, map_one] using integerValue_eq_one
    exact congrArg Units.val valueGroupValue_eq_one
  · intro h
    have valueGroupValue_eq_one : valueGroupValue = 1 := Units.ext h
    have integerValue_eq_one : integerValue = 1 := by
      change Units.map _ valueGroupValue = 1
      rw [valueGroupValue_eq_one, map_one]
    simpa only [map_one] using
      congrArg WithZero.unitsWithZeroEquiv integerValue_eq_one

private theorem localFieldUnitValuation_eq_one_of_roots
    (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (value : Fˣ) (roots : HasAllPositiveRoots value) :
    localFieldUnitValuation F value = 1 := by
  apply multiplicativeInt_eq_one_of_roots
  intro n hn
  obtain ⟨root, root_pow⟩ := roots n hn
  exact ⟨localFieldUnitValuation F root, by rw [← map_pow, root_pow]⟩

private noncomputable def valuationRingUnitOfFieldUnit
    (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (value : Fˣ) (valuation_eq_one : valuation F (value : F) = 1) :
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

theorem fieldUnit_eq_one_of_roots
    (F : Type*) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (value : Fˣ) (roots : HasAllPositiveRoots value) : value = 1 := by
  have value_valuation_eq_one : valuation F (value : F) = 1 :=
    (localFieldUnitValuation_eq_one_iff F value).mp
      (localFieldUnitValuation_eq_one_of_roots F value roots)
  let integralValue :=
    valuationRingUnitOfFieldUnit F value value_valuation_eq_one
  have integralRoots : HasAllPositiveRoots integralValue := by
    intro n hn
    obtain ⟨root, root_pow⟩ := roots n hn
    have root_valuation_hom_pow : (localFieldUnitValuation F root) ^ n = 1 := by
      rw [← map_pow, root_pow,
        localFieldUnitValuation_eq_one_of_roots F value roots]
    have root_valuation_hom_eq_one : localFieldUnitValuation F root = 1 :=
      (pow_eq_one_iff_left hn.ne').mp root_valuation_hom_pow
    have root_valuation_eq_one : valuation F (root : F) = 1 :=
      (localFieldUnitValuation_eq_one_iff F root).mp root_valuation_hom_eq_one
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
    (fun unit : (Valuation.integer (valuation F))ˣ ↦
      (((unit : Valuation.integer (valuation F)) : F)))
    integralValue_eq_one
  simpa [integralValue, valuationRingUnitOfFieldUnit] using equality

theorem MultiplicativeKummerMap.injective_of_localField
    (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {C : Type u} [CommGroup C]
    (kummerMap : MultiplicativeKummerMap Fˣ C) :
    Function.Injective kummerMap.hom :=
  kummerMap.injective_of_roots_eq_one (fieldUnit_eq_one_of_roots F)

end LocalFieldKummerRigidity

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localFieldKummerRigidity : Obligation :=
  { id := "IUT-II.local-field-Gm-kummer-rigidity"
    source :=
      "Absolute Anabelian Topics III, Definition 1.5 G_m prerequisite; IUT II Kummer theory"
    status := VerificationStatus.proved
    note :=
      "For the full multiplicative group of an actual nonarchimedean local field, " ++
        "an element admitting roots of every positive degree is proved to be one: " ++
        "the discrete valuation vanishes and the valuation-ring unit is controlled " ++
        "by a profinite residual-finiteness argument. A Kummer map with the standard " ++
        "kernel characterization is therefore injective. No arbitrary-torus or " ++
        "semi-abelian Kummer-faithfulness theorem is claimed."
    dependsOn := ["IUT-II.times-mu-ism-orbit"] }

end LeanFormal.IUT.Audit
