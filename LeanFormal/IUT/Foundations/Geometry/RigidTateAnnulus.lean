/-
  The first genuine rigid-analytic Tate layer.

  This file does not identify an elliptic curve with a Tate quotient.  It
  constructs the analytic domain on which that identification is defined.
  In particular, all powers are indexed by `ℤ`; replacing the domain by a
  single finite quotient would lose the annular geometry used by the Tate
  functions.
-/

import LeanFormal.IUT.Audit.Status
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace LeanFormal.IUT

universe u

noncomputable section

namespace RigidTate

variable {K : Type u} [NormedField K]

/-- A contracting Tate parameter in a normed field. -/
structure Parameter where
  q : K
  q_ne_zero : q ≠ 0
  q_norm_pos : 0 < ‖q‖
  q_norm_lt_one : ‖q‖ < 1

namespace Parameter

variable (P : Parameter (K := K))

theorem q_norm_ne_zero : ‖P.q‖ ≠ 0 := ne_of_gt P.q_norm_pos

theorem q_ne_one : P.q ≠ 1 := by
  intro h
  have hnorm : ‖P.q‖ < 1 := P.q_norm_lt_one
  rw [h] at hnorm
  norm_num at hnorm

theorem q_pow_ne_zero (n : ℕ) : P.q ^ n ≠ 0 :=
  pow_ne_zero n P.q_ne_zero

theorem q_zpow_ne_zero (n : ℤ) : P.q ^ n ≠ 0 :=
  zpow_ne_zero n P.q_ne_zero

theorem norm_q_zpow (n : ℤ) : ‖P.q ^ n‖ = ‖P.q‖ ^ n := by
  exact norm_zpow P.q n

theorem norm_q_zpow_pos (n : ℤ) : 0 < ‖P.q‖ ^ n := by
  exact zpow_pos P.q_norm_pos n

theorem norm_q_zpow_lt_one (n : ℤ) (hn : 0 < n) :
    ‖P.q‖ ^ n < 1 := by
  exact zpow_lt_one₀ P.q_norm_pos P.q_norm_lt_one hn

theorem norm_q_zpow_gt_one (n : ℤ) (hn : n < 0) :
    1 < ‖P.q‖ ^ n := by
  have hrepr : n = -(-n) := by omega
  rw [hrepr, zpow_neg]
  apply (one_lt_inv₀ (Parameter.norm_q_zpow_pos P (-n))).2
  exact Parameter.norm_q_zpow_lt_one P (-n) (by omega)

theorem norm_q_zpow_mul (m n : ℤ) :
    ‖P.q‖ ^ (m + n) = ‖P.q‖ ^ m * ‖P.q‖ ^ n := by
  rw [zpow_add₀ (ne_of_gt P.q_norm_pos)]

end Parameter

/-- The closed annulus with radial bounds `|q|^(n+1)` and `|q|^n`.

  The strict inequalities are intentional: the Tate Laurent series has no
  pole on this domain.  `n` records the annulus and is not erased by a
  quotient or by a finite label.
-/
def Shell (P : Parameter (K := K)) (n : ℤ) :=
  {u : K // u ≠ 0 ∧ ‖P.q‖ ^ (n + 1) < ‖u‖ ∧ ‖u‖ < ‖P.q‖ ^ n}

namespace Shell

variable (P : Parameter (K := K)) (n : ℤ)

@[simp] theorem val_mk (u : K) (hu : u ≠ 0)
    (hinner : ‖P.q‖ ^ (n + 1) < ‖u‖)
    (houter : ‖u‖ < ‖P.q‖ ^ n) :
    (⟨u, hu, hinner, houter⟩ : Shell P n).1 = u :=
  rfl

theorem ne_zero (u : Shell P n) : u.1 ≠ 0 := u.property.1

theorem inner (u : Shell P n) :
    ‖P.q‖ ^ (n + 1) < ‖u.1‖ := u.property.2.1

theorem outer (u : Shell P n) :
    ‖u.1‖ < ‖P.q‖ ^ n := u.property.2.2

theorem norm_pos (u : Shell P n) : 0 < ‖u.1‖ :=
  norm_pos_iff.mpr u.ne_zero

theorem mem (u : K) : u ∈ Set.range (fun x : Shell P n => x.1) ↔
    u ≠ 0 ∧ ‖P.q‖ ^ (n + 1) < ‖u‖ ∧ ‖u‖ < ‖P.q‖ ^ n := by
  constructor
  · rintro ⟨x, rfl⟩
    exact x.property
  · rintro ⟨hu, hinner, houter⟩
    exact ⟨⟨u, hu, hinner, houter⟩, rfl⟩

end Shell

/-- Multiplication by `q^m` moves the `n`-th shell to the `(m+n)`-th shell. -/
def shellAction (P : Parameter (K := K)) (m n : ℤ) (u : Shell P n) : Shell P (m + n) := by
  have hq : 0 < ‖P.q‖ := P.q_norm_pos
  have hq0 : ‖P.q‖ ≠ 0 := ne_of_gt hq
  have hu : 0 < ‖u.1‖ := Shell.norm_pos P n u
  have hmul : ‖P.q ^ m * u.1‖ = ‖P.q‖ ^ m * ‖u.1‖ := by
    rw [norm_mul, Parameter.norm_q_zpow]
  refine ⟨P.q ^ m * u.1, ?_, ?_, ?_⟩
  · exact mul_ne_zero (Parameter.q_zpow_ne_zero P m) (Shell.ne_zero P n u)
  · rw [hmul]
    calc
      ‖P.q‖ ^ (m + n + 1) =
          ‖P.q‖ ^ m * ‖P.q‖ ^ (n + 1) := by
            rw [show m + n + 1 = m + (n + 1) by ring,
              Parameter.norm_q_zpow_mul]
      _ < ‖P.q‖ ^ m * ‖u.1‖ :=
        mul_lt_mul_of_pos_left (Shell.inner P n u)
          (Parameter.norm_q_zpow_pos P m)
  · rw [hmul]
    calc
      ‖P.q‖ ^ m * ‖u.1‖ < ‖P.q‖ ^ m * ‖P.q‖ ^ n :=
        mul_lt_mul_of_pos_left (Shell.outer P n u)
          (Parameter.norm_q_zpow_pos P m)
      _ = ‖P.q‖ ^ (m + n) := by
        rw [Parameter.norm_q_zpow_mul]

@[simp] theorem shellAction_val (P : Parameter (K := K)) (m n : ℤ)
    (u : Shell P n) :
    (shellAction P m n u).1 = P.q ^ m * u.1 :=
  rfl

theorem shellAction_ne_zero (P : Parameter (K := K)) (m n : ℤ)
    (u : Shell P n) : (shellAction P m n u).1 ≠ 0 :=
  Shell.ne_zero P (m + n) (shellAction P m n u)

theorem shellAction_inner (P : Parameter (K := K)) (m n : ℤ)
    (u : Shell P n) :
    ‖P.q‖ ^ (m + n + 1) < ‖(shellAction P m n u).1‖ :=
  Shell.inner P (m + n) (shellAction P m n u)

theorem shellAction_outer (P : Parameter (K := K)) (m n : ℤ)
    (u : Shell P n) :
    ‖(shellAction P m n u).1‖ < ‖P.q‖ ^ (m + n) :=
  Shell.outer P (m + n) (shellAction P m n u)

theorem shellAction_injective (P : Parameter (K := K)) (m n : ℤ) :
    Function.Injective (shellAction P m n) := by
  intro u v h
  apply Subtype.ext
  have hv := congrArg (fun x : Shell P (m + n) => x.1) h
  dsimp [shellAction] at hv
  exact (mul_left_cancel₀ (Parameter.q_zpow_ne_zero P m) hv)

theorem shellAction_comp_val (P : Parameter (K := K))
    (m₁ m₂ n : ℤ) (u : Shell P n) :
    (shellAction P m₁ (m₂ + n) (shellAction P m₂ n u)).1 =
      (shellAction P (m₁ + m₂) n u).1 := by
  simp only [shellAction_val]
  rw [← mul_assoc, ← zpow_add₀ P.q_ne_zero]

end RigidTate

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def rigidTateAnnulus : Obligation :=
  { id := "Foundations.Geometry.rigid-tate-annulus"
    source := "Tate uniformization: annular domain and q^Z transport"
    status := VerificationStatus.proved
    note :=
      "The normed-field shell carrying the strict inequalities " ++
        "|q|^(n+1) < |u| < |q|^n is constructed. Integer q-powers move " ++
        "shells by proved equivalences, with nonzero denominators and no " ++
        "finite-label collapse. This is the analytic domain/action layer; " ++
        "the Laurent coordinate identity, elliptic-curve point map, and " ++
        "Galois-equivariant Tate uniformization are not claimed here."
    dependsOn := [ "Foundations.Geometry.tate-curve-q-series" ] }

end LeanFormal.IUT.Audit
