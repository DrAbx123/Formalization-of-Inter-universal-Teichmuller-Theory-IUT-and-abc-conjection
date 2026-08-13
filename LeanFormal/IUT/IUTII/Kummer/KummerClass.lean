/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.NatRootSystem

/-!
  Kummer classes from compatible root systems.

  This is the unit-valued cocycle layer appearing before the paper's full
  Frobenioid and etale Kummer isomorphisms.  The construction is source-facing:
  a Galois action on units and a root system of a fixed unit produce a
  compatible tower of roots of unity.  The class law and change-of-roots law
  are proved here; H¹ identification and local ramification remain later
  obligations.
-/

namespace LeanFormal.IUT

structure CyclotomicTower (M : Type*) [CommMonoid M] where
  component : Nat → Mˣ
  torsion : ∀ n : Nat, component n ^ n = 1
  transition : ∀ n k : Nat, k ≠ 0 → component (n * k) ^ k = component n

namespace CyclotomicTower

variable {M : Type*} [CommMonoid M]

def one : CyclotomicTower M where
  component _ := 1
  torsion _ := by simp
  transition _ _ _ := by simp

def mul (first second : CyclotomicTower M) : CyclotomicTower M where
  component n := first.component n * second.component n
  torsion n := by simp [mul_pow, first.torsion, second.torsion]
  transition n k hk := by
    simp only [mul_pow, first.transition n k hk, second.transition n k hk]

@[ext] theorem ext {first second : CyclotomicTower M}
    (h : ∀ n, first.component n = second.component n) : first = second := by
  cases first
  cases second
  simp only at h
  congr
  funext n
  exact h n

end CyclotomicTower

namespace KummerClass

variable {G M : Type*} [Group G] [CommMonoid M]
variable (ρ : G →* (Mˣ ≃* Mˣ))
variable {value : Mˣ} (r : NatRootSystem value)

def action (σ : G) (tower : CyclotomicTower M) : CyclotomicTower M where
  component n := ρ σ (tower.component n)
  torsion n := by
    rw [← map_pow, tower.torsion, map_one]
  transition n k hk := by
    rw [← map_pow, tower.transition n k hk]

def kummerClass
    (fixed : ∀ σ : G, ρ σ value = value) (σ : G) : CyclotomicTower M where
  component n := ρ σ (r.root n) / r.root n
  torsion n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hnum : ρ σ (r.root n) ^ n = value := by
        rw [← map_pow, r.pow_self n hn, fixed σ]
      rw [div_pow, hnum, r.pow_self n hn]
      simp
  transition n k hk := by
    have hnum : ρ σ (r.root (n * k)) ^ k = ρ σ (r.root n) := by
      rw [← map_pow, r.compat n k hk]
    rw [div_pow, hnum, r.compat n k hk]

@[simp] theorem kummerClass_component
    (fixed : ∀ σ : G, ρ σ value = value) (σ : G) (n : Nat) :
    (kummerClass ρ r fixed σ).component n = ρ σ (r.root n) / r.root n := rfl

theorem kummerClass_one
    (fixed : ∀ σ : G, ρ σ value = value) :
    kummerClass ρ r fixed 1 = CyclotomicTower.one := by
  apply CyclotomicTower.ext
  intro n
  simp [kummerClass_component, CyclotomicTower.one]

theorem kummerClass_mul
    (fixed : ∀ σ : G, ρ σ value = value) (σ τ : G) :
    kummerClass ρ r fixed (σ * τ) =
      CyclotomicTower.mul
        (action ρ σ (kummerClass ρ r fixed τ))
        (kummerClass ρ r fixed σ) := by
  apply CyclotomicTower.ext
  intro n
  change ρ (σ * τ) (r.root n) / r.root n =
    ρ σ (ρ τ (r.root n) / r.root n) *
      (ρ σ (r.root n) / r.root n)
  rw [map_mul ρ σ τ]
  have hpoint : (ρ σ * ρ τ) (r.root n) =
      ρ σ (ρ τ (r.root n)) := rfl
  rw [hpoint]
  rw [map_div]
  exact (div_mul_div_cancel _ _ _).symm

def rootSystemDiff (first second : NatRootSystem value) : CyclotomicTower M where
  component n := second.root n / first.root n
  torsion n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [div_pow, first.pow_self n hn, second.pow_self n hn]
      simp
  transition n k hk := by
    rw [div_pow, first.compat n k hk, second.compat n k hk]

theorem kummerClass_diff
    (fixed : ∀ σ : G, ρ σ value = value)
    (first second : NatRootSystem value) (σ : G) :
    CyclotomicTower.mul
        (kummerClass ρ second fixed σ)
        (rootSystemDiff first second) =
      CyclotomicTower.mul
        (kummerClass ρ first fixed σ)
        (action ρ σ (rootSystemDiff first second)) := by
  apply CyclotomicTower.ext
  intro n
  change
    (ρ σ (second.root n) / second.root n) *
        (second.root n / first.root n) =
      (ρ σ (first.root n) / first.root n) *
        ρ σ (second.root n / first.root n)
  rw [map_div]
  calc
    (ρ σ (second.root n) / second.root n) *
        (second.root n / first.root n) =
      ρ σ (second.root n) / first.root n := div_mul_div_cancel _ _ _
    _ = (ρ σ (second.root n) / ρ σ (first.root n)) *
        (ρ σ (first.root n) / first.root n) := by
      rw [div_mul_div_cancel]
    _ = (ρ σ (first.root n) / first.root n) *
        (ρ σ (second.root n) / ρ σ (first.root n)) := by
      ac_rfl

end KummerClass

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def kummerClass : Obligation :=
  { id := "IUT-II.kummer-class-cocycle"
    source := "IUT II, Kummer-theoretic Galois evaluation; IUT III, Proposition 3.5"
    status := VerificationStatus.provedKernel
    note :=
      "A compatible unit root system produces a cyclotomic tower; the " ++
        "unit class identity, crossed multiplication law, and change-of-root " ++
        "coboundary equation are proved. H¹ identification, arithmetic " ++
        "integrality, ramification, and the paper's Kummer isomorphism remain " ++
        "pending."
    dependsOn := [ "IUT-II.natural-compatible-root-system",
      "IUT-II.kummer-root-ratio-contract" ] }

end LeanFormal.IUT.Audit
