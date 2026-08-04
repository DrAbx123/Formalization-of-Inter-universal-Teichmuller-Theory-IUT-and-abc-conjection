import LeanFormal.IUT.IUTII.Frobenioid.LocalTorsionUnits
import LeanFormal.IUT.IUTII.Kummer.RationalRootSystem
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

/-!
  The torsion-cyclotomic structure of the local integral monoid.

  The rational-circle construction is adapted from `promachina/iut-lean`,
  `Iut/Foundations/SourceThetaEvaluation.lean`, at audited commit
  `2eb61e1b037635a5346f7265f520b458155303ed` (Apache-2.0).  It identifies
  `Q/Z`, in multiplicative notation, with all finite-order units in an
  algebraic closure of a characteristic-zero field.

  Combining this with the proved integral-torsion equivalence gives the
  torsion-cyclotomic structure required by the local `TM` model.  Independently,
  the proved groupification equivalence transports divisibility of algebraic
  closure units back to the Grothendieck group of the integral monoid.
-/

namespace LeanFormal.IUT

universe u

namespace RationalCircleCyclotome

/-- The inclusion `Q/Z -> R/Z` induced by the rational embedding. -/
noncomputable def rationalToRealCircle :
    AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map
    (AddSubgroup.zmultiples (1 : ℚ))
    (AddSubgroup.zmultiples (1 : ℝ))
    (Rat.castHom ℝ).toAddMonoidHom
    (by
      intro value hvalue
      rw [AddSubgroup.mem_zmultiples_iff] at hvalue
      rcases hvalue with ⟨integer, rfl⟩
      change
        (Rat.castHom ℝ).toAddMonoidHom (integer • (1 : ℚ)) ∈
          AddSubgroup.zmultiples (1 : ℝ)
      rw [map_zsmul]
      have hone :
          (Rat.castHom ℝ).toAddMonoidHom (1 : ℚ) = 1 := by
        norm_num
      rw [hone]
      change integer • (1 : ℝ) ∈ AddSubgroup.zmultiples (1 : ℝ)
      rw [AddSubgroup.mem_zmultiples_iff]
      exact ⟨integer, rfl⟩)

@[simp]
theorem rationalToRealCircle_mk (q : ℚ) :
    rationalToRealCircle (q : AddCircle (1 : ℚ)) =
      ((q : ℝ) : AddCircle (1 : ℝ)) :=
  QuotientAddGroup.map_mk' _ _ _ _ q

theorem rationalToRealCircle_injective :
    Function.Injective rationalToRealCircle := by
  intro first second h
  induction first using QuotientAddGroup.induction_on with
  | _ first =>
    induction second using QuotientAddGroup.induction_on with
    | _ second =>
      rw [rationalToRealCircle_mk,
        rationalToRealCircle_mk,
        QuotientAddGroup.eq_iff_sub_mem] at h
      rw [QuotientAddGroup.eq_iff_sub_mem]
      rw [AddSubgroup.mem_zmultiples_iff] at h ⊢
      rcases h with ⟨integer, hinteger⟩
      refine ⟨integer, ?_⟩
      apply Rat.cast_injective (α := ℝ)
      simpa using hinteger

/-- Exponentiation embeds the multiplicative rational circle in `C^x`. -/
noncomputable def rationalCircleToComplexUnits :
    Multiplicative (AddCircle (1 : ℚ)) →* ℂˣ where
  toFun value := Circle.toUnits
    (AddCircle.toCircle (rationalToRealCircle value.toAdd))
  map_one' := by simp [rationalToRealCircle]
  map_mul' first second := by
    change Circle.toUnits
        (AddCircle.toCircle
          (rationalToRealCircle (first.toAdd + second.toAdd))) = _
    rw [map_add, AddCircle.toCircle_add, map_mul]

@[simp]
theorem rationalCircleToComplexUnits_mk (q : ℚ) :
    rationalCircleToComplexUnits
        (Multiplicative.ofAdd (q : AddCircle (1 : ℚ))) =
      Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * (q : ℝ)))
        (Complex.exp_ne_zero _) := by
  apply Units.ext
  simp [rationalCircleToComplexUnits, AddCircle.toCircle_apply_mk]
  ring_nf

theorem rationalCircle_isOfFinOrder
    (value : Multiplicative (AddCircle (1 : ℚ))) :
    IsOfFinOrder value := by
  change IsOfFinAddOrder value.toAdd
  induction value.toAdd using QuotientAddGroup.induction_on with
  | _ q =>
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨q.den, q.pos, ?_⟩
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
    rw [Rat.den_mul_eq_num]
    apply (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr
    exact ⟨q.num, by simp⟩

theorem rationalCircleToComplexUnits_injective :
    Function.Injective rationalCircleToComplexUnits := by
  intro first second equality
  apply Multiplicative.toAdd.injective
  apply rationalToRealCircle_injective
  apply AddCircle.injective_toCircle one_ne_zero
  apply Subtype.ext
  exact congrArg Units.val equality

noncomputable def rationalCircleToComplexTorsion :
    Multiplicative (AddCircle (1 : ℚ)) →*
      CommGroup.torsion ℂˣ where
  toFun value :=
    ⟨rationalCircleToComplexUnits value,
      (CommGroup.mem_torsion (rationalCircleToComplexUnits value)).mpr
        (rationalCircleToComplexUnits.isOfFinOrder
          (rationalCircle_isOfFinOrder value))⟩
  map_one' := Subtype.ext (map_one rationalCircleToComplexUnits)
  map_mul' first second :=
    Subtype.ext (map_mul rationalCircleToComplexUnits first second)

theorem rationalCircleToComplexTorsion_bijective :
    Function.Bijective rationalCircleToComplexTorsion := by
  constructor
  · intro first second equality
    apply rationalCircleToComplexUnits_injective
    exact congrArg Subtype.val equality
  · intro target
    rcases isOfFinOrder_iff_pow_eq_one.mp
        ((CommGroup.mem_torsion (target : ℂˣ)).mp target.property) with
      ⟨n, hn, hpow⟩
    letI : NeZero n := ⟨hn.ne'⟩
    have hroot : (target : ℂˣ) ∈ rootsOfUnity n ℂ := by
      rw [mem_rootsOfUnity]
      exact hpow
    rcases (Complex.mem_rootsOfUnity n (target : ℂˣ)).mp hroot with
      ⟨i, _hi, heq⟩
    let q : ℚ := (i : ℚ) / (n : ℚ)
    refine
      ⟨Multiplicative.ofAdd
          (q : AddCircle (1 : ℚ)), ?_⟩
    apply Subtype.ext
    change
      rationalCircleToComplexUnits
          (Multiplicative.ofAdd (q : AddCircle (1 : ℚ))) =
        (target : ℂˣ)
    rw [rationalCircleToComplexUnits_mk]
    apply Units.ext
    change Complex.exp (2 * Real.pi * Complex.I * (q : ℝ)) =
      (target : ℂˣ)
    simpa [q] using heq

noncomputable def rationalCircleMulEquivComplexTorsion :
    Multiplicative (AddCircle (1 : ℚ)) ≃*
      CommGroup.torsion ℂˣ :=
  MulEquiv.ofBijective rationalCircleToComplexTorsion
    rationalCircleToComplexTorsion_bijective

/-- A field embedding restricted to finite-order units. -/
noncomputable def torsionUnitsMap
    {F E : Type*} [Field F] [Field E]
    (embedding : F →+* E) :
    CommGroup.torsion Fˣ →* CommGroup.torsion Eˣ where
  toFun value :=
    ⟨Units.map embedding.toMonoidHom value,
      (CommGroup.mem_torsion
        (Units.map embedding.toMonoidHom (value : Fˣ))).mpr
        ((Units.map embedding.toMonoidHom).isOfFinOrder
          ((CommGroup.mem_torsion (value : Fˣ)).mp value.property))⟩
  map_one' := Subtype.ext (map_one (Units.map embedding.toMonoidHom))
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul (Units.map embedding.toMonoidHom)
      (first : Fˣ) (second : Fˣ)

/-- An embedding of algebraically closed characteristic-zero fields is
bijective on all finite-order units. -/
theorem torsionUnitsMap_bijective
    {F E : Type*} [Field F] [Field E]
    [IsAlgClosed F] [IsAlgClosed E]
    [CharZero F] [CharZero E]
    (embedding : F →+* E) :
    Function.Bijective (torsionUnitsMap embedding) := by
  constructor
  · intro first second equality
    apply Subtype.ext
    apply Units.ext
    apply embedding.injective
    change
      embedding ((first : Fˣ) : F) =
        embedding ((second : Fˣ) : F)
    exact congrArg (fun value : CommGroup.torsion Eˣ =>
      ((value : Eˣ) : E)) equality
  · intro target
    rcases isOfFinOrder_iff_pow_eq_one.mp
        ((CommGroup.mem_torsion (target : Eˣ)).mp target.property) with
      ⟨n, hn, hpow⟩
    letI : NeZero n := ⟨hn.ne'⟩
    let targetRoot : rootsOfUnity n E :=
      ⟨(target : Eˣ), by
        rw [mem_rootsOfUnity]
        exact hpow⟩
    have rootMapInjective :
        Function.Injective (restrictRootsOfUnity embedding n) := by
      intro first second equality
      apply Subtype.ext
      apply Units.map_injective embedding.injective
      exact congrArg Subtype.val equality
    have rootMapBijective :
        Function.Bijective (restrictRootsOfUnity embedding n) :=
      rootMapInjective.bijective_of_nat_card_le
        (by
          rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity E n,
            HasEnoughRootsOfUnity.natCard_rootsOfUnity F n])
    rcases rootMapBijective.surjective targetRoot with
      ⟨sourceRoot, hsourceRoot⟩
    let sourceTorsion : CommGroup.torsion Fˣ :=
      ⟨(sourceRoot : Fˣ),
        (CommGroup.mem_torsion (sourceRoot : Fˣ)).mpr
          (isOfFinOrder_iff_pow_eq_one.mpr
            ⟨n, hn, (mem_rootsOfUnity _ _).mp sourceRoot.property⟩)⟩
    refine ⟨sourceTorsion, ?_⟩
    apply Subtype.ext
    change
      Units.map embedding.toMonoidHom (sourceRoot : Fˣ) =
        (target : Eˣ)
    exact congrArg Subtype.val hsourceRoot

noncomputable def torsionUnitsMapEquiv
    {F E : Type*} [Field F] [Field E]
    [IsAlgClosed F] [IsAlgClosed E]
    [CharZero F] [CharZero E]
    (embedding : F →+* E) :
    CommGroup.torsion Fˣ ≃* CommGroup.torsion Eˣ :=
  MulEquiv.ofBijective (torsionUnitsMap embedding)
    (torsionUnitsMap_bijective embedding)

/-- The roots of unity in any algebraic closure of a characteristic-zero
field form the multiplicative rational circle. -/
noncomputable def rationalCircleMulEquivAlgebraicClosureUnitsTorsion
    (K : Type u) [Field K] [CharZero K] :
    Multiplicative (AddCircle (1 : ℚ)) ≃*
      CommGroup.torsion (AlgebraicClosure K)ˣ := by
  letI : Algebra ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.instAlgebra ℚ
  let qbarToComplex : AlgebraicClosure ℚ →+* ℂ :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom
  let qbarToKbar : AlgebraicClosure ℚ →+* AlgebraicClosure K :=
    (IsAlgClosed.lift :
      AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom
  exact
    rationalCircleMulEquivComplexTorsion.trans
      ((torsionUnitsMapEquiv qbarToComplex).symm.trans
        (torsionUnitsMapEquiv qbarToKbar))

end RationalCircleCyclotome

namespace LocalIntegralMonoid

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Divisibility of algebraic-closure units transported to the groupification
of the local integral monoid. -/
@[implicit_reducible]
noncomputable def groupificationRootableByNat :
    RootableBy
      (Algebra.GrothendieckGroup (LocalIntegralMonoid p)) ℕ := by
  letI : RootableBy (AlgebraicClosure ℚ_[p])ˣ ℕ :=
    AlgebraicClosureRootSystem.unitsRootableByNat
  let equivalence := groupificationEquivAlgebraicClosureUnits p
  exact
    rootableByOfPowLeftSurj _ _
      fun {n} n_ne_zero value => by
        obtain ⟨root, root_pow⟩ :=
          RootableBy.surjective_pow
            ((AlgebraicClosure ℚ_[p])ˣ) ℕ
            n_ne_zero (equivalence value)
        refine ⟨equivalence.symm root, ?_⟩
        apply equivalence.injective
        simpa using root_pow

/-- One compatible rational-root system in the actual local groupification. -/
noncomputable def groupificationCompatibleRoots
    (value : Algebra.GrothendieckGroup (LocalIntegralMonoid p)) :
    CompatibleRootSystem
      (Algebra.GrothendieckGroup (LocalIntegralMonoid p)) value := by
  letI : RootableBy
      (Algebra.GrothendieckGroup (LocalIntegralMonoid p)) ℕ :=
    groupificationRootableByNat p
  exact CompatibleRootSystem.ofRootable value

/-- The torsion units of the local integral monoid are exactly `Q/Z`. -/
noncomputable def torsionCyclotomicEquiv :
    CommGroup.torsion (LocalIntegralMonoid p)ˣ ≃*
      Multiplicative (AddCircle (1 : ℚ)) :=
  (torsionEquivAlgebraicClosureTorsion p).trans
    (RationalCircleCyclotome.rationalCircleMulEquivAlgebraicClosureUnitsTorsion
      ℚ_[p]).symm

/-- The nonempty cyclotomic structure required by the algebraic presentation
of the local `TM` model. -/
theorem torsionCyclotomic :
    Nonempty
      (CommGroup.torsion (LocalIntegralMonoid p)ˣ ≃*
        Multiplicative (AddCircle (1 : ℚ))) :=
  ⟨torsionCyclotomicEquiv p⟩

end LocalIntegralMonoid

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localTorsionCyclotome : Obligation :=
  { id := "IUT-II.local-torsion-cyclotome"
    source := "Absolute Anabelian Topics III, Definition 3.1(i); local MLF TM model"
    status := VerificationStatus.proved
    note :=
      "The multiplicative rational circle Q/Z is proved equivalent to all " ++
        "finite-order units in the algebraic closure of Q_p, using finite " ++
        "roots-of-unity groups in characteristic zero. Composing with the " ++
        "proved integral-unit torsion equivalence gives the actual local " ++
        "torsion-cyclotomic structure. The Grothendieck groupification is also " ++
        "proved rootable in every positive natural degree and supplies one " ++
        "compatible rational-root system."
    dependsOn :=
      [ "IUT-II.local-torsion-unit-equivalence",
        "IUT-II.compatible-rational-roots-from-divisibility" ] }

end LeanFormal.IUT.Audit
