/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
  A reusable quotient by one cyclic subgroup.

  IUT uses the same `q^Z` pattern in several places.  The carrier here is
  deliberately only a group quotient; no topology, geometry, or choice of
  representatives is built into it.  Specialized Tate files instantiate
  this API with algebraic-closure units.
-/

namespace LeanFormal

universe u v

namespace CyclicQuotient

variable {G : Type u} [CommGroup G]

abbrev cyclicSubgroup (g : G) : _root_.Subgroup G :=
  _root_.Subgroup.zpowers g

abbrev Carrier (g : G) := G ⧸ cyclicSubgroup g

def quotientClass (g x : G) : Carrier g :=
  QuotientGroup.mk x

@[simp] theorem quotientClass_mk (g x : G) :
    quotientClass g x = QuotientGroup.mk x := rfl

theorem mem_iff (g x : G) :
    x ∈ cyclicSubgroup g ↔ ∃ n : ℤ, x = g ^ n := by
  rw [_root_.Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, h⟩
    exact ⟨n, h.symm⟩
  · rintro ⟨n, h⟩
    exact ⟨n, h.symm⟩

theorem quotientClass_eq_iff_mem (g x y : G) :
    quotientClass g x = quotientClass g y ↔ x / y ∈ cyclicSubgroup g := by
  exact QuotientGroup.eq_iff_div_mem

theorem quotientClass_eq_iff_power (g x y : G) :
    quotientClass g x = quotientClass g y ↔ ∃ n : ℤ, x / y = g ^ n := by
  rw [quotientClass_eq_iff_mem, mem_iff]

theorem quotientClass_eq_one_iff_mem (g x : G) :
    quotientClass g x = 1 ↔ x ∈ cyclicSubgroup g := by
  exact QuotientGroup.eq_one_iff (N := cyclicSubgroup g) x

theorem quotientClass_eq_one_iff_power (g x : G) :
    quotientClass g x = 1 ↔ ∃ n : ℤ, x = g ^ n := by
  rw [quotientClass_eq_one_iff_mem, mem_iff]

theorem quotientClass_mul (g x y : G) :
    quotientClass g (x * y) = quotientClass g x * quotientClass g y := rfl

theorem quotientClass_inv (g x : G) :
    quotientClass g x⁻¹ = (quotientClass g x)⁻¹ := rfl

theorem quotientClass_pow (g x : G) (n : ℕ) :
    quotientClass g (x ^ n) = quotientClass g x ^ n := by
  induction n with
  | zero => simp [quotientClass]
  | succ n ih =>
      rw [pow_succ, quotientClass_mul, ih, pow_succ]

theorem quotientClass_zpow (g x : G) (n : ℤ) :
    quotientClass g (x ^ n) = quotientClass g x ^ n := by
  cases n with
  | ofNat n =>
      change quotientClass g (x ^ (n : ℤ)) =
        quotientClass g x ^ (n : ℤ)
      rw [zpow_natCast, zpow_natCast]
      exact quotientClass_pow g x n
  | negSucc n =>
      simp [zpow_negSucc]

theorem quotientClass_power (g : G) (x : G) (m n : ℤ) :
    quotientClass g (x ^ (m + n)) =
      quotientClass g (x ^ m) * quotientClass g (x ^ n) := by
  rw [zpow_add, quotientClass_mul]

theorem quotientClass_power_sub (g : G) (x : G) (m n : ℤ) :
    quotientClass g (x ^ (m - n)) =
      quotientClass g (x ^ m) / quotientClass g (x ^ n) := by
  rw [sub_eq_add_neg, zpow_add, zpow_neg,
    quotientClass_mul, quotientClass_inv]
  simp [div_eq_mul_inv]

theorem quotientClass_mul_power (g x : G) (n : ℤ) :
    quotientClass g (x * g ^ n) = quotientClass g x := by
  apply (quotientClass_eq_iff_power g (x * g ^ n) x).mpr
  refine ⟨n, ?_⟩
  simp [div_eq_mul_inv, mul_assoc]

theorem quotientClass_power_mul (g x : G) (n : ℤ) :
    quotientClass g (g ^ n * x) = quotientClass g x := by
  simpa only [mul_comm] using quotientClass_mul_power g x n

theorem quotientClass_div_power (g x : G) (n : ℤ) :
    quotientClass g (x / g ^ n) = quotientClass g x := by
  simpa only [div_eq_mul_inv, zpow_neg] using quotientClass_mul_power g x (-n)

theorem quotientClass_representative (g x : G) (n : ℤ) :
    quotientClass g (x * g ^ n) = quotientClass g x :=
  quotientClass_mul_power g x n

theorem quotientClass_representative_iff (g x y : G) :
    quotientClass g x = quotientClass g y ↔ ∃ n : ℤ, x = y * g ^ n := by
  constructor
  · intro h
    rcases (quotientClass_eq_iff_power g x y).mp h with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc
      x = (x / y) * y := by simp [div_eq_mul_inv, mul_assoc]
      _ = (g ^ n) * y := by rw [hn]
      _ = y * g ^ n := by ac_rfl
  · rintro ⟨n, rfl⟩
    exact quotientClass_representative g y n

theorem quotientClass_cancel_left (g x y z : G)
    (h : quotientClass g x * quotientClass g y =
      quotientClass g x * quotientClass g z) :
    quotientClass g y = quotientClass g z :=
  mul_left_cancel h

theorem quotientClass_cancel_right (g x y z : G)
    (h : quotientClass g y * quotientClass g x =
      quotientClass g z * quotientClass g x) :
    quotientClass g y = quotientClass g z :=
  mul_right_cancel h

theorem quotientClass_power_one (g : G) (n : ℤ) :
    quotientClass g (g ^ n) = 1 := by
  rw [quotientClass_eq_one_iff_power]
  exact ⟨n, rfl⟩

section Descent

variable {H : Type v} [CommGroup H]

def descend (g : G) (φ : G →* H) (hg : φ g = 1) :
    Carrier g →* H :=
  QuotientGroup.lift (cyclicSubgroup g) φ (by
    intro x hx
    rcases _root_.Subgroup.mem_zpowers_iff.mp hx with ⟨n, hn⟩
    change φ x = 1
    rw [← hn, map_zpow, hg, one_zpow])

@[simp] theorem descend_quotientClass (g : G) (φ : G →* H)
    (hg : φ g = 1) (x : G) :
    descend g φ hg (quotientClass g x) = φ x := by
  exact QuotientGroup.lift_mk' _ _ x

theorem descend_power (g : G) (φ : G →* H) (hg : φ g = 1)
    (n : ℤ) : descend g φ hg (quotientClass g (g ^ n)) = 1 := by
  rw [descend_quotientClass, map_zpow, hg, one_zpow]

theorem descend_eq_of_class_eq (g : G) (φ : G →* H)
    (hg : φ g = 1) (x y : G)
    (h : quotientClass g x = quotientClass g y) : φ x = φ y := by
  rw [← descend_quotientClass g φ hg x, ← descend_quotientClass g φ hg y]
  exact congrArg (descend g φ hg) h

theorem descend_surjective (g : G) (φ : G →* H)
    (hg : φ g = 1) (hφ : Function.Surjective φ) :
    Function.Surjective (descend g φ hg) := by
  intro y
  rcases hφ y with ⟨x, rfl⟩
  exact ⟨quotientClass g x, descend_quotientClass g φ hg x⟩

end Descent

end CyclicQuotient

end LeanFormal
