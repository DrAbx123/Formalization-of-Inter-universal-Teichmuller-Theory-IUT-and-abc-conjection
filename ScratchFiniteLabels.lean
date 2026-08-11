import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic
import Init.Omega

open scoped Pointwise

abbrev Fl (l : Nat) := ZMod l
def lStar (l : Nat) : Nat := (l - 1) / 2

variable (l : Nat) [Fact l.Prime]

theorem two_ne_zero_Fl (hl5 : 5 ≤ l) : (2 : Fl l) ≠ 0 := by
  have h : ((2 : Nat) : ZMod l) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod l) l]
    intro hdvd
    have hle : l ≤ 2 := Nat.le_of_dvd (by omega) hdvd
    omega
  simpa using h

theorem orderOf_neg_one_units (hl5 : 5 ≤ l) :
    orderOf (-1 : (ZMod l)ˣ) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : (-1 : (ZMod l)ˣ) ≠ 1 := by
    intro h
    rw [Units.ext_iff] at h
    simp only [Units.val_neg, Units.val_one] at h
    have h2 : (2 : ZMod l) = 0 := by
      have h2' := congrArg (fun z : ZMod l => z + 1) h
      simpa [one_add_one_eq_two, add_assoc, add_left_comm, add_comm] using h2'.symm
    exact two_ne_zero_Fl l hl5 h2
  have hsq : (-1 : (ZMod l)ˣ) ^ 2 = 1 := neg_one_sq
  exact orderOf_eq_prime hsq hne

abbrev negSubgroup (l : Nat) [Fact l.Prime] : Subgroup (ZMod l)ˣ :=
  Subgroup.zpowers (-1)

theorem card_negSubgroup (hl5 : 5 ≤ l) :
    Nat.card (negSubgroup l) = 2 := by
  rw [Nat.card_eq_fintype_card]
  let f : Fin 2 → negSubgroup l :=
    Fin.cases ⟨1, (negSubgroup l).one_mem⟩
      (fun i => Fin.cases
        ⟨(-1 : (ZMod l)ˣ), Subgroup.mem_zpowers _⟩
        (fun j => Fin.elim0 j) i)
  have hne : (-1 : (ZMod l)ˣ) ≠ 1 := by
    intro h
    rw [Units.ext_iff] at h
    simp only [Units.val_neg, Units.val_one] at h
    have h2 : (2 : ZMod l) = 0 := by
      have h2' := congrArg (fun z : ZMod l => z + 1) h
      simpa [one_add_one_eq_two, add_assoc, add_left_comm, add_comm] using h2'.symm
    exact two_ne_zero_Fl l hl5 h2
  have hf : Function.Bijective f := by
    constructor
    · intro i j
      have hi := Fin.eq_zero_or_eq_succ i
      have hj := Fin.eq_zero_or_eq_succ j
      rcases hi with rfl | ⟨i, rfl⟩
      · rcases hj with rfl | ⟨j, rfl⟩
        · rfl
        · have hj0 : j = 0 := Fin.eq_zero j
          subst j
          exfalso
          apply hne
          exact congrArg Subtype.val (show f 0 = f 1 from ‹f 0 = f 1›)
      · have hi0 : i = 0 := Fin.eq_zero i
        subst i
        rcases hj with rfl | ⟨j, rfl⟩
        · exfalso
          apply hne
          exact congrArg Subtype.val (show f 1 = f 0 from ‹f 1 = f 0›)
        · have hj0 : j = 0 := Fin.eq_zero j
          subst j
          rfl
    · intro x
      have hx : x.1 ∈ Subgroup.zpowers (-1) := x.2
      rcases (Subgroup.mem_zpowers_iff.mp hx) with ⟨k, hk⟩
      have hmod := zpow_mod_orderOf (-1 : (ZMod l)ˣ) k
      rw [orderOf_neg_one_units l hl5] at hmod
      rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
      · refine ⟨0, ?_⟩
        apply Subtype.ext
        calc
          x.1 = (-1 : (ZMod l)ˣ) ^ k := hk.symm
          _ = (-1 : (ZMod l)ˣ) ^ (k % 2) := hmod.symm
          _ = 1 := by rw [hk0]; norm_num
          _ = (f 0).1 := by rfl
      · refine ⟨1, ?_⟩
        apply Subtype.ext
        calc
          x.1 = (-1 : (ZMod l)ˣ) ^ k := hk.symm
          _ = (-1 : (ZMod l)ˣ) ^ (k % 2) := hmod.symm
          _ = -1 := by rw [hk1]; norm_num
          _ = (f 1).1 := by rfl
  exact Fintype.card_congr (Equiv.ofBijective f hf)
