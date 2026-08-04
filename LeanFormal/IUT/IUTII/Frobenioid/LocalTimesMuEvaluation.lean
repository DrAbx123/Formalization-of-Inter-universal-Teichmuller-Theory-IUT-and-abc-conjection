import LeanFormal.IUT.IUTII.Frobenioid.LocalTorsionUnits
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient

/-!
  The local unit evaluation after passage to the `times-μ` quotient.

  The integral closure carrier supplies the source unit group, while the
  ambient algebraic-closure units supply the target used by the local
  F-prime strip.  Torsion maps to torsion, so the evaluation descends by the
  quotient-group universal property.  The descended map is proved equivariant
  for the local absolute Galois action.  No surjectivity or global
  Frobenioid identification is asserted here.
-/

namespace LeanFormal.IUT

namespace LocalIntegralMonoid

variable (p : Nat) [Fact (Nat.Prime p)]

noncomputable def timesMuUnitEvaluation :
    TimesMuQuotient (LocalIntegralMonoid p)ˣ →*
      TimesMuQuotient (AlgebraicClosure ℚ_[p])ˣ :=
  QuotientGroup.map
    (CommGroup.torsion (LocalIntegralMonoid p)ˣ)
    (CommGroup.torsion (AlgebraicClosure ℚ_[p])ˣ)
    (unitEvaluation p)
    (CommGroup.le_comap_torsion (unitEvaluation p))

@[simp]
theorem timesMuUnitEvaluation_quotientMap
    (unit : (LocalIntegralMonoid p)ˣ) :
    timesMuUnitEvaluation p (TimesMuQuotient.quotientMap unit) =
      TimesMuQuotient.quotientMap (unitEvaluation p unit) := by
  rfl

theorem timesMuUnitEvaluation_equivariant
    (g : LocalAbsoluteGalois p)
    (x : TimesMuQuotient (LocalIntegralMonoid p)ˣ) :
    timesMuUnitEvaluation p
        (TimesMuQuotient.action (unitAction p) g x) =
      TimesMuQuotient.action (localGaloisUnitsAction p) g
        (timesMuUnitEvaluation p x) := by
  obtain ⟨unit, rfl⟩ := TimesMuQuotient.quotientMap_surjective x
  rw [timesMuUnitEvaluation_quotientMap,
    TimesMuQuotient.action_quotientMap,
    timesMuUnitEvaluation_quotientMap,
    TimesMuQuotient.action_quotientMap,
    unitEvaluation_equivariant]

theorem timesMuUnitEvaluation_injective :
    Function.Injective (timesMuUnitEvaluation p) := by
  intro first second equality
  obtain ⟨firstUnit, rfl⟩ :=
    TimesMuQuotient.quotientMap_surjective first
  obtain ⟨secondUnit, rfl⟩ :=
    TimesMuQuotient.quotientMap_surjective second
  rw [timesMuUnitEvaluation_quotientMap,
    timesMuUnitEvaluation_quotientMap] at equality
  apply QuotientGroup.eq_iff_div_mem.mpr
  have targetTorsion :
      unitEvaluation p (firstUnit / secondUnit) ∈
        CommGroup.torsion (AlgebraicClosure ℚ_[p])ˣ := by
    have quotientDifference :=
      QuotientGroup.eq_iff_div_mem.mp equality
    simpa only [map_div] using quotientDifference
  apply (CommGroup.mem_torsion (firstUnit / secondUnit)).mpr
  apply (unitEvaluation_injective p).isOfFinOrder_iff.mp
  exact (CommGroup.mem_torsion
    (unitEvaluation p (firstUnit / secondUnit))).mp targetTorsion

end LocalIntegralMonoid

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localTimesMuEvaluation : Obligation :=
  { id := "IUT-II.local-times-mu-evaluation"
    source := "IUT II, Definition 4.9(i); local Frobenioid evaluation carrier"
    status := VerificationStatus.proved
    note :=
      "The unit evaluation from the nonzero integral-closure carrier descends " ++
        "to the torsion (`times-μ`) quotient by Mathlib's quotient-group map. " ++
        "The descended map is injective and its local absolute Galois " ++
        "equivariance is proved. Surjectivity, the " ++
        "ind-topology, and the global group/Frobenioid Kummer isomorphism remain " ++
        "separate obligations."
    dependsOn :=
      [ "IUT-II.local-integral-monoid-carrier",
        "IUT-II.times-mu-torsion-quotient" ] }

end LeanFormal.IUT.Audit
