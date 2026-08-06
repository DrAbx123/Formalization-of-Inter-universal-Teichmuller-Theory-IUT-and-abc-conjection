/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Foundations.Geometry.TateCurve
import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
  The first module of the concrete Tate prerequisite batch.

  It contains only the actual local q=p element and the canonical q-series
  curve.  No Kummer, reduction, or curve-point uniformization claim is made
  here; those are separate modules in the same bottom-up batch.
-/

namespace LeanFormal.IUT

noncomputable section

structure ConcreteTateParameter (l : PrimeGeFive)
    [Fact (Nat.Prime l.value)] where
  q : ℚ_[l.value]
  q_eq_prime : q = (l.value : ℚ_[l.value])
  q_ne_zero : q ≠ 0
  q_norm_lt_one : ‖q‖ < 1
  curve : WeierstrassCurve ℚ_[l.value]
  curve_eq_canonical :
    curve = TateCurve.weierstrassCurve ℚ_[l.value] q
  lambert_summable : ∀ weight : Nat,
    Summable (fun n : Nat ↦
      (n : ℚ_[l.value]) ^ weight * q ^ n / (1 - q ^ n))

namespace ConcreteTateParameter

variable (l : PrimeGeFive) [Fact (Nat.Prime l.value)]

noncomputable def canonical : ConcreteTateParameter l := by
  letI := l.factPrime
  let q : ℚ_[l.value] := l.value
  refine
    { q := q
      q_eq_prime := rfl
      q_ne_zero := ?_
      q_norm_lt_one := ?_
      curve := TateCurve.weierstrassCurve ℚ_[l.value] q
      curve_eq_canonical := rfl
      lambert_summable := ?_ }
  · exact Nat.cast_ne_zero.mpr l.prime.ne_zero
  · exact Padic.norm_p_lt_one
  · intro weight
    exact TateCurve.lambertSeries_summable ℚ_[l.value] weight
      Padic.norm_p_lt_one

@[simp] theorem canonical_q : (canonical l).q = (l.value : ℚ_[l.value]) :=
  (canonical l).q_eq_prime

theorem canonical_q_ne_one : (canonical l).q ≠ 1 := by
  letI := l.factPrime
  intro h
  have hnorm := (canonical l).q_norm_lt_one
  rw [h] at hnorm
  norm_num at hnorm

theorem q_ne_one
    (P : ConcreteTateParameter l) : P.q ≠ 1 := by
  intro h
  have hnorm := P.q_norm_lt_one
  rw [h] at hnorm
  norm_num at hnorm

theorem canonical_curve_eq :
    (canonical l).curve = TateCurve.weierstrassCurve ℚ_[l.value]
      (canonical l).q :=
  (canonical l).curve_eq_canonical

theorem q_power_norm_lt_one
    (P : ConcreteTateParameter l) (n : Nat) (hn : 0 < n) :
    ‖P.q ^ n‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg P.q) P.q_norm_lt_one hn.ne'

theorem q_power_ne_zero
    (P : ConcreteTateParameter l) (n : Nat) : P.q ^ n ≠ 0 := by
  exact pow_ne_zero n P.q_ne_zero

theorem q_power_ne_one
    (P : ConcreteTateParameter l) (n : Nat) (hn : 0 < n) :
    P.q ^ n ≠ 1 := by
  intro h
  have hnorm := q_power_norm_lt_one l P n hn
  rw [h] at hnorm
  norm_num at hnorm

noncomputable def qUnit
    (P : ConcreteTateParameter l) :
    (AlgebraicClosure ℚ_[l.value])ˣ :=
  Units.map
    (algebraMap (ℚ_[l.value]) (AlgebraicClosure ℚ_[l.value])).toMonoidHom
    (Units.mk0 P.q P.q_ne_zero)

theorem qUnit_ne_one
    (P : ConcreteTateParameter l) : P.qUnit ≠ 1 := by
  intro h
  apply P.q_ne_one
  apply FaithfulSMul.algebraMap_injective
    (ℚ_[l.value]) (AlgebraicClosure ℚ_[l.value])
  have hv := congrArg Units.val h
  simpa [qUnit] using hv

theorem canonical_qUnit_eq_localParameter :
    (canonical l).qUnit = localQParameterFor l.value := by
  apply Units.ext
  rfl

theorem qUnit_pow
    (P : ConcreteTateParameter l) (n : Nat) :
    (P.qUnit) ^ n =
      Units.map
        (algebraMap (ℚ_[l.value]) (AlgebraicClosure ℚ_[l.value])).toMonoidHom
    (Units.mk0 (P.q ^ n) (q_power_ne_zero l P n)) := by
  apply Units.ext
  simp [qUnit]

end ConcreteTateParameter

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteTateParameter : Obligation :=
  { id := "Foundations.Geometry.concrete-tate-parameter"
    source := "IUT I, Definition 3.1(c); local q-parameter"
    status := VerificationStatus.proved
    note :=
      "For every prime label l >= 5, the actual element q=l in Q_l, its " ++
        "strict p-adic contraction, canonical Tate q-series curve, and all " ++
        "Lambert-series summability obligations are constructed and proved. " ++
        "This module does not identify the curve with an arithmetic input " ++
        "curve and does not assert Tate uniformization."
    dependsOn := [ "Foundations.Geometry.tate-curve-q-series",
      "Foundations.Arithmetic.prime-label-ge-five" ] }

end LeanFormal.IUT.Audit
