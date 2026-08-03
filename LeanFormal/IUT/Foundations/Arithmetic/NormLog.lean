import LeanFormal.IUT.Audit.Status
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

/-!
  Norm/log arithmetic for units of a normed field.

  This is the ordinary multiplicative-to-additive calculation used by local
  degree maps.  It is deliberately independent of p-adic fields, Frobenioids,
  and IUT source data: any later local realization must instantiate this
  kernel rather than restate its multiplication law.
-/

namespace LeanFormal.IUT

noncomputable def unitNormLogDegree (K : Type*) [NormedField K] : Kˣ →* Multiplicative Real where
  toFun := fun u =>
    Multiplicative.ofAdd (Real.log ‖(u : K)‖)
  map_one' := by
    apply Multiplicative.ext
    simp
  map_mul' := by
    intro u v
    apply Multiplicative.ext
    rw [Units.val_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (Units.ne_zero u))
        (norm_ne_zero_iff.mpr (Units.ne_zero v))]
    rw [← ofAdd_add]

theorem unitNormLogDegree_apply_mul (K : Type*) [NormedField K]
    (u v : Kˣ) :
    unitNormLogDegree K (u * v) =
      unitNormLogDegree K u * unitNormLogDegree K v := by
  exact (unitNormLogDegree K).map_mul u v

theorem unitNormLogDegree_apply_one (K : Type*) [NormedField K] :
    unitNormLogDegree K (1 : Kˣ) = 1 := by
  exact (unitNormLogDegree K).map_one

theorem norm_pos_unit (K : Type*) [NormedField K] (u : Kˣ) :
    0 < ‖(u : K)‖ :=
  (norm_pos_iff.mpr (Units.ne_zero u))

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def normLogArithmetic : Obligation :=
  { id := "Foundations.Arithmetic.norm-log"
    source := "Standard norm multiplicativity and real logarithm arithmetic"
    status := VerificationStatus.proved
    note :=
      "For units of every normed field, the norm followed by Real.log is " ++
        "packaged as a MonoidHom into Multiplicative Real. The p-adic local " ++
        "carrier instantiates this theorem; no valuation or Frobenioid claim " ++
        "is included."
    dependsOn := [] }

end LeanFormal.IUT.Audit
