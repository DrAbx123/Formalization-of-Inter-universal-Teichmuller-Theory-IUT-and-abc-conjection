/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.CompatibleRoots

/-!
  The source-facing Kummer root-ratio contract.

  The fields mirror the root-ratio input used in the Kummer realization: a
  group acts on a commutative arithmetic group, a chosen root system is fixed
  by the subgroup, and the Galois-translated root differs by a unit.  The
  concrete arithmetic monoid, its Grothendieck group, and the integrality proof
  are intentionally separate lower-layer obligations.
-/

namespace LeanFormal.IUT

structure KummerRootRatioData
    (G M U : Type*) [Group G] [CommGroup M] [CommGroup U]
    (value : M) where
  subgroup : Subgroup G
  action : G →* M ≃* M
  fixed : ∀ g : subgroup, action (g : G) value = value
  rootSystem : CompatibleRootSystem M value
  ratioUnit : subgroup → ℚ → U
  ratioMap : U →* M
  ratio_spec :
    ∀ (g : subgroup) (q : ℚ),
      ratioMap (ratioUnit g q) =
        action (g : G) (rootSystem.roots q).toMul /
          (rootSystem.roots q).toMul

namespace KummerRootRatioData

variable {G M U : Type*} [Group G] [CommGroup M] [CommGroup U]
  {value : M}

theorem ratioUnit_zero
    (D : KummerRootRatioData G M U value)
    (injective_ratioMap : Function.Injective D.ratioMap)
    (g : D.subgroup) : D.ratioUnit g 0 = 1 := by
  apply injective_ratioMap
  rw [D.ratio_spec]
  simp

theorem ratioUnit_add
    (D : KummerRootRatioData G M U value)
    (injective_ratioMap : Function.Injective D.ratioMap)
    (g : D.subgroup) (q₁ q₂ : ℚ) :
    D.ratioUnit g (q₁ + q₂) = D.ratioUnit g q₁ * D.ratioUnit g q₂ := by
  apply injective_ratioMap
  rw [map_mul, D.ratio_spec, D.ratio_spec, D.ratio_spec]
  have hroots := congrArg Additive.toMul (D.rootSystem.roots.map_add q₁ q₂)
  change (D.rootSystem.roots (q₁ + q₂)).toMul =
    (D.rootSystem.roots q₁).toMul * (D.rootSystem.roots q₂).toMul at hroots
  rw [hroots, map_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

end KummerRootRatioData

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def kummerRootRatio : Obligation :=
  { id := "IUT-II.kummer-root-ratio-contract"
    source := "IUT II, Kummer-theoretic Galois root ratios; IUT III, Proposition 3.5"
    status := VerificationStatus.interface
    note :=
      "The source-facing fixed-subgroup/root-system/unit-ratio fields and " ++
        "their formal zero/addition consequences are recorded. The IUT " ++
        "arithmetic monoid, unit embedding, integrality, cyclotomic descent, " ++
        "and crossed-homomorphism laws remain pending."
    dependsOn := [ "IUT-II.compatible-rational-root-system",
      "IUT-I-II.local-f-prime-strip-carrier" ] }

end LeanFormal.IUT.Audit
