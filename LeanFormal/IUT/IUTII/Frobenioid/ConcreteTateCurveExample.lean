import LeanFormal.IUT.Foundations.Geometry.TateCurve
import LeanFormal.IUT.IUTII.Frobenioid.ConcreteLocalKummerExample
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
  A concrete canonical Tate equation at the selected local parameter `q = 5`.

  The equation is indexed by the same element used by the local Kummer
  realization.  This proves the q-series convergence and exact parameter
  reuse; it does not claim ellipticity or Tate uniformization.
-/

namespace LeanFormal.IUT

noncomputable section

local instance fivePrimeFact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

noncomputable def concreteTateQ : ℚ_[5] := 5

theorem concreteTateQ_ne_zero : concreteTateQ ≠ 0 := by
  exact Nat.cast_ne_zero.mpr Nat.prime_five.ne_zero

theorem concreteTateQ_norm_lt_one : ‖concreteTateQ‖ < 1 := by
  exact Padic.norm_p_lt_one

theorem concreteTateQ_is_localQParameter :
    (concreteTateQ : ℚ_[5]) =
      (localQParameterFor 5 : AlgebraicClosure ℚ_[5]) := by
  rfl

noncomputable def concreteTateCurve : WeierstrassCurve ℚ_[5] :=
  TateCurve.weierstrassCurve ℚ_[5] concreteTateQ

theorem concreteTateCurve_lambertSeries_summable (weight : Nat) :
    Summable
      (fun n : Nat ↦
        (n : ℚ_[5]) ^ weight * concreteTateQ ^ n /
          (1 - concreteTateQ ^ n)) := by
  exact TateCurve.lambertSeries_summable ℚ_[5] weight concreteTateQ_norm_lt_one

theorem concreteTateCurve_a1 : concreteTateCurve.a₁ = 1 := by
  rfl

theorem concreteTateCurve_q_is_same_as_kummer_parameter :
    algebraMap ℚ_[5] (AlgebraicClosure ℚ_[5]) concreteTateQ =
      (localQParameterFor 5 : AlgebraicClosure ℚ_[5]) := by
  rfl

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteTateCurveQParameter : Obligation :=
  { id := "IUT-I-II.concrete-tate-q-series-at-five"
    source := "IUT I, Definition 3.1(c); selected local q-parameter"
    status := VerificationStatus.testCarrier
    note :=
      "The canonical Tate q-series equation over Q_5 is instantiated at " ++
        "the same q=5 element used by the proved local Kummer realization. " ++
        "Only convergence and parameter identity are proved; no ellipticity, " ++
        "uniformization, or Frobenioid recognition is asserted."
    dependsOn :=
      [ "Foundations.Geometry.tate-curve-q-series",
        "IUT-II.concrete-local-q-parameter-roots" ] }

end LeanFormal.IUT.Audit
