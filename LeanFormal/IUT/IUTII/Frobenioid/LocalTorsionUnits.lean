import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralMonoid
import Mathlib.GroupTheory.Torsion

/-!
  Torsion units of the local integral-closure monoid.

  This proof is adapted from `promachina/iut-lean`,
  `Iut/Foundations/SourceThetaEvaluation.lean`, at audited commit
  `ea91200be2a0a6287ade838553127f68ec38d864` (Apache-2.0).  It is specialized
  to Mathlib's `Q_p` carrier and current local names.

  Every finite-order unit of the algebraic closure is integral together with
  its inverse.  Consequently the inclusion of integral-monoid units induces
  an equivalence on full torsion subgroups.
-/

namespace LeanFormal.IUT

namespace LocalIntegralMonoid

variable (p : Nat) [Fact (Nat.Prime p)]

theorem unitEvaluation_injective :
    Function.Injective (unitEvaluation p) := by
  intro first second equality
  apply Units.ext
  apply Subtype.ext
  apply Subtype.ext
  have underlying := congrArg Units.val equality
  change
    (first.val.1.1 : AlgebraicClosure ℚ_[p]) =
      (second.val.1.1 : AlgebraicClosure ℚ_[p]) at underlying
  exact underlying

noncomputable def torsionUnit
    (value : (AlgebraicClosure ℚ_[p])ˣ)
    (n : Nat) (n_ne_zero : n ≠ 0)
    (value_pow : value ^ n = 1) :
    (LocalIntegralMonoid p)ˣ := by
  let baseRing := Valuation.integer (ValuativeRel.valuation ℚ_[p])
  have value_integral :
      IsIntegral baseRing (value : AlgebraicClosure ℚ_[p]) := by
    apply IsIntegral.of_pow (Nat.pos_of_ne_zero n_ne_zero)
    rw [← Units.val_pow_eq_pow_val, value_pow]
    exact isIntegral_one
  have inverse_pow : value⁻¹ ^ n = 1 := by
    rw [inv_pow, value_pow, inv_one]
  have inverse_integral :
      IsIntegral baseRing (value⁻¹ : AlgebraicClosure ℚ_[p]) := by
    apply IsIntegral.of_pow (Nat.pos_of_ne_zero n_ne_zero)
    have inverse_pow_value := congrArg Units.val inverse_pow
    have inverse_pow_base :
        ((value : AlgebraicClosure ℚ_[p])⁻¹) ^ n = 1 := by
      simpa only [Units.val_pow_eq_pow_val,
        Units.val_inv_eq_inv_val, Units.val_one] using inverse_pow_value
    rw [inverse_pow_base]
    exact isIntegral_one
  let integralValue : LocalAlgebraicIntegerRing p :=
    ⟨value, value_integral⟩
  let integralInverse : LocalAlgebraicIntegerRing p :=
    ⟨value⁻¹, inverse_integral⟩
  let monoidValue : LocalIntegralMonoid p :=
    ⟨integralValue,
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        intro equality
        exact value.ne_zero (congrArg Subtype.val equality))⟩
  let monoidInverse : LocalIntegralMonoid p :=
    ⟨integralInverse,
      mem_nonZeroDivisors_iff_ne_zero.mpr (by
        intro equality
        have underlying :=
          congrArg
            (fun z : LocalAlgebraicIntegerRing p =>
              (z : AlgebraicClosure ℚ_[p])) equality
        simp only [integralInverse] at underlying
        apply value⁻¹.ne_zero
        rw [Units.val_inv_eq_inv_val]
        exact underlying)⟩
  exact
    { val := monoidValue
      inv := monoidInverse
      val_inv := by
        apply Subtype.ext
        apply Subtype.ext
        simp [monoidValue, monoidInverse,
          integralValue, integralInverse]
      inv_val := by
        apply Subtype.ext
        apply Subtype.ext
        simp [monoidValue, monoidInverse,
          integralValue, integralInverse] }

@[simp]
theorem unitEvaluation_torsionUnit
    (value : (AlgebraicClosure ℚ_[p])ˣ)
    (n : Nat) (n_ne_zero : n ≠ 0)
    (value_pow : value ^ n = 1) :
    unitEvaluation p (torsionUnit p value n n_ne_zero value_pow) = value := by
  apply Units.ext
  change
    ((torsionUnit p value n n_ne_zero value_pow).val.1.1 :
      AlgebraicClosure ℚ_[p]) =
      (value : AlgebraicClosure ℚ_[p])
  rfl

noncomputable def torsionToAlgebraicClosureTorsion :
    CommGroup.torsion (LocalIntegralMonoid p)ˣ →*
      CommGroup.torsion (AlgebraicClosure ℚ_[p])ˣ where
  toFun value :=
    ⟨unitEvaluation p value,
      (CommGroup.mem_torsion (unitEvaluation p value)).mpr
        ((unitEvaluation p).isOfFinOrder
          ((CommGroup.mem_torsion (value : (LocalIntegralMonoid p)ˣ)).mp
            value.property))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul (unitEvaluation p)
      (first : (LocalIntegralMonoid p)ˣ)
      (second : (LocalIntegralMonoid p)ˣ)

theorem torsionToAlgebraicClosureTorsion_bijective :
    Function.Bijective (torsionToAlgebraicClosureTorsion p) := by
  constructor
  · intro first second equality
    apply Subtype.ext
    apply unitEvaluation_injective p
    exact congrArg Subtype.val equality
  · intro target
    rcases isOfFinOrder_iff_pow_eq_one.mp
        ((CommGroup.mem_torsion
          (target : (AlgebraicClosure ℚ_[p])ˣ)).mp
          target.property) with
      ⟨n, hn, hpow⟩
    let sourceUnit := torsionUnit
      p (target : (AlgebraicClosure ℚ_[p])ˣ) n hn.ne' hpow
    have sourcePower : sourceUnit ^ n = 1 := by
      apply unitEvaluation_injective p
      rw [map_pow, map_one, unitEvaluation_torsionUnit, hpow]
    let sourceTorsion :
        CommGroup.torsion (LocalIntegralMonoid p)ˣ :=
      ⟨sourceUnit,
        (CommGroup.mem_torsion sourceUnit).mpr
          (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, sourcePower⟩)⟩
    refine ⟨sourceTorsion, ?_⟩
    apply Subtype.ext
    exact unitEvaluation_torsionUnit
      p (target : (AlgebraicClosure ℚ_[p])ˣ) n hn.ne' hpow

noncomputable def torsionEquivAlgebraicClosureTorsion :
    CommGroup.torsion (LocalIntegralMonoid p)ˣ ≃*
      CommGroup.torsion (AlgebraicClosure ℚ_[p])ˣ :=
  MulEquiv.ofBijective
    (torsionToAlgebraicClosureTorsion p)
    (torsionToAlgebraicClosureTorsion_bijective p)

end LocalIntegralMonoid

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localTorsionUnits : Obligation :=
  { id := "IUT-II.local-torsion-unit-equivalence"
    source := "IUT II, Definition 4.9(i); roots of unity in the local model monoid"
    status := VerificationStatus.proved
    note :=
      "Every finite-order algebraic-closure unit and its inverse are proved " ++
        "integral over the Q_p valuation ring. The inclusion of local integral " ++
        "monoid units is injective and induces a proved multiplicative " ++
        "equivalence of the two full torsion subgroups."
    dependsOn := [ "IUT-II.local-integral-monoid-carrier" ] }

end LeanFormal.IUT.Audit
