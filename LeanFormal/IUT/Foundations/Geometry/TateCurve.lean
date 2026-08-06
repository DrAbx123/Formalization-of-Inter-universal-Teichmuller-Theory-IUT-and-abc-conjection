import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import LeanFormal.IUT.Audit.Status

/-!
  The canonical q-indexed Tate Weierstrass equation.

  This is the convergent Lambert-series construction.  It gives the
  canonical algebraic equation attached to a contracting parameter, but it
  deliberately does not assert analytic uniformization or identify the
  equation with a separately supplied elliptic curve.

  Source comparison: IUT I, Definition 3.1(c); the q-series core follows the
  audited `promachina/iut-lean` source file `SourceTateCurve.lean`.
-/

namespace LeanFormal.IUT

universe u

noncomputable section

namespace TateCurve

/-- The Lambert series `s_k(q) = sum n^k q^n / (1 - q^n)`. -/
noncomputable def lambertSeries
    (K : Type u) [NormedField K] (weight : Nat) (q : K) : K :=
  ∑' n : Nat, (n : K) ^ weight * q ^ n / (1 - q ^ n)

/-- A strict contraction makes every Lambert series summable. -/
theorem lambertSeries_summable
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (weight : Nat) {q : K} (hq : ‖q‖ < 1) :
    Summable
      (fun n : Nat ↦
        (n : K) ^ weight * q ^ n / (1 - q ^ n)) := by
  simpa only [Nat.cast_pow] using
    (summable_norm_pow_mul_geometric_div_one_sub weight hq)

/-- The `a4` coefficient of the canonical Tate equation. -/
noncomputable def a4
    (K : Type u) [NormedField K] (q : K) : K :=
  -5 * lambertSeries K 3 q

/-- The `a6` coefficient of the canonical Tate equation. -/
noncomputable def a6
    (K : Type u) [NormedField K] [CharZero K] (q : K) : K :=
  -(5 * lambertSeries K 3 q + 7 * lambertSeries K 5 q) / 12

/-- The canonical equation `y^2 + xy = x^3 + a4(q) x + a6(q)`. -/
noncomputable def weierstrassCurve
    (K : Type u) [NormedField K] [CharZero K]
    (q : K) : WeierstrassCurve K :=
  WeierstrassCurve.mk 1 0 0 (a4 K q) (a6 K q)

@[simp] theorem weierstrassCurve_a1
    (K : Type u) [NormedField K] [CharZero K] (q : K) :
    (weierstrassCurve K q).a₁ = 1 :=
  rfl

@[simp] theorem weierstrassCurve_a2
    (K : Type u) [NormedField K] [CharZero K] (q : K) :
    (weierstrassCurve K q).a₂ = 0 :=
  rfl

@[simp] theorem weierstrassCurve_a3
    (K : Type u) [NormedField K] [CharZero K] (q : K) :
    (weierstrassCurve K q).a₃ = 0 :=
  rfl

@[simp] theorem weierstrassCurve_a4
    (K : Type u) [NormedField K] [CharZero K] (q : K) :
    (weierstrassCurve K q).a₄ = a4 K q :=
  rfl

@[simp] theorem weierstrassCurve_a6
    (K : Type u) [NormedField K] [CharZero K] (q : K) :
    (weierstrassCurve K q).a₆ = a6 K q :=
  rfl

end TateCurve

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def tateCurveQSeriesKernel : Obligation :=
  { id := "Foundations.Geometry.tate-curve-q-series"
    source := "IUT I, Definition 3.1(c); canonical Tate q-series"
    status := VerificationStatus.proved
    note :=
      "The Lambert-series coefficients and the canonical q-indexed " ++
        "Weierstrass equation are defined over a complete normed field, and " ++
        "summability is proved for every strict contraction. The ellipticity, " ++
        "Tate uniformization, Galois equivariance, and identification with an " ++
        "arithmetic input curve remain separate obligations."
    dependsOn := [] }

end LeanFormal.IUT.Audit
