import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic

/-!
  Concrete finite label objects used in the source papers.

  This module is deliberately limited to standard finite algebra.  It defines
  `F_l` as `ZMod l`, assumes the paper's explicit condition that `l` is a
  prime at least five, and proves the elementary cardinality and sign facts.
  It does not claim to construct a Hodge theater or an etale theta function.

  Source correspondence: IUT I, Sections 4 and 6; the finite-label part of
  Takkun-kohinata/IUT_LEAN `IutLean/Combinatorics/Fl.lean`.
-/

namespace LeanFormal.IUT

open scoped Pointwise

abbrev Fl (l : Nat) := ZMod l

def lStar (l : Nat) : Nat := (l - 1) / 2

section Prime

variable (l : Nat) [Fact l.Prime]

instance : NeZero l :=
  ⟨(Fact.out : Nat.Prime l).pos.ne'⟩

theorem card_Fl : Fintype.card (Fl l) = l :=
  ZMod.card l

end Prime

section Odd

variable (l : Nat)

theorem two_mul_lStar_add_one (hodd : Odd l) :
    2 * lStar l + 1 = l := by
  obtain ⟨k, rfl⟩ := hodd
  unfold lStar
  omega

theorem card_compl_zero (hodd : Odd l) [Fact l.Prime] :
    Fintype.card {x : Fl l // x ≠ 0} = 2 * lStar l := by
  have hcompl : Fintype.card {x : Fl l // x ≠ 0} =
      Fintype.card (Fl l) - Fintype.card {x : Fl l // x = 0} :=
    Fintype.card_subtype_compl (fun x : Fl l => x = 0)
  rw [Fintype.card_subtype_eq, card_Fl] at hcompl
  have hprime : Nat.Prime l := Fact.out
  have hne_two : l ≠ 2 := by
    intro hl
    subst l
    norm_num at hodd
  have hodd' : Odd l := hprime.odd_of_ne_two hne_two
  have hstar := two_mul_lStar_add_one l hodd'
  omega

end Odd

section Sign

variable (l : Nat) [Fact l.Prime]

theorem two_ne_zero_Fl (hl5 : 5 ≤ l) : (2 : Fl l) ≠ 0 := by
  have h : ((2 : Nat) : ZMod l) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod l) l]
    intro hdvd
    have hle : l ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  simpa using h

theorem neg_eq_self_iff (hl5 : 5 ≤ l) (x : Fl l) :
    -x = x ↔ x = 0 := by
  constructor
  · intro h
    have hxx : x + x = 0 := add_eq_zero_iff_eq_neg.mpr h.symm
    have h2x : (2 : Fl l) * x = 0 := by
      rw [two_mul]
      exact hxx
    rcases mul_eq_zero.mp h2x with h0 | h0
    · exact absurd h0 (two_ne_zero_Fl l hl5)
    · exact h0
  · rintro rfl
    simp

end Sign

section MultiplicativeLabels

variable (l : Nat) [Fact l.Prime]

def negSubgroup : Subgroup (ZMod l)ˣ :=
  Subgroup.zpowers (-1)

theorem orderOf_neg_one_units (hl5 : 5 ≤ l) :
    orderOf (-1 : (ZMod l)ˣ) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : (-1 : (ZMod l)ˣ) ≠ 1 := by
    intro h
    rw [Units.ext_iff] at h
    simp only [Units.val_neg, Units.val_one] at h
    have h2 : (2 : ZMod l) = 0 := by
      linear_combination -h
    exact two_ne_zero_Fl l hl5 h2
  have hsq : (-1 : (ZMod l)ˣ) ^ 2 = 1 := neg_one_sq
  exact orderOf_eq_prime hsq hne

abbrev LabCusp := (ZMod l)ˣ ⧸ negSubgroup l

theorem card_LabCusp (hl5 : 5 ≤ l) :
    Nat.card (LabCusp l) = lStar l := by
  change Nat.card ((ZMod l)ˣ ⧸ negSubgroup l) = lStar l
  have hlag : Nat.card (ZMod l)ˣ =
      Nat.card ((ZMod l)ˣ ⧸ negSubgroup l) * Nat.card (negSubgroup l) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (negSubgroup l)
  have hG : Nat.card (ZMod l)ˣ = l - 1 := by
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card_units l
  have hH : Nat.card (negSubgroup l) = 2 := by
    rw [negSubgroup, Nat.card_zpowers]
    exact orderOf_neg_one_units l hl5
  have hodd : Odd l := (Fact.out : l.Prime).odd_of_ne_two (by omega)
  have hstar := two_mul_lStar_add_one l hodd
  rw [hG, hH] at hlag
  omega

end MultiplicativeLabels

end LeanFormal.IUT
