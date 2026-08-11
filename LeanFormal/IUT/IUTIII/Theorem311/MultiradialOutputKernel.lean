import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.UpperSemi
import Mathlib.Data.Set.Finite.Basic

namespace LeanFormal.IUT

open scoped BigOperators

universe u v

namespace MultiradialKernel

structure Core (Label : Type u) (Choice : Type v) [AddGroup Label] where
  base : Choice
  level : Choice → Nat
  ind1 : Label → Choice → Choice
  ind2 : Label → Choice → Choice
  ind3 : Nat → Choice → Choice
  ind1_zero : ∀ c, ind1 0 c = c
  ind1_add : ∀ g h c, ind1 (g + h) c = ind1 h (ind1 g c)
  ind1_inverse : ∀ g c, ind1 (-g) (ind1 g c) = c
  ind2_zero : ∀ c, ind2 0 c = c
  ind2_add : ∀ g h c, ind2 (g + h) c = ind2 h (ind2 g c)
  ind2_inverse : ∀ g c, ind2 (-g) (ind2 g c) = c
  ind3_zero : ∀ c, ind3 0 c = c
  ind3_add : ∀ m n c, ind3 (m + n) c = ind3 n (ind3 m c)
  ind1_ind2_commute : ∀ g h c, ind1 g (ind2 h c) = ind2 h (ind1 g c)
  ind1_ind3_commute : ∀ g n c, ind1 g (ind3 n c) = ind3 n (ind1 g c)
  ind2_ind3_commute : ∀ g n c, ind2 g (ind3 n c) = ind3 n (ind2 g c)
  ind1_level : ∀ g c, level (ind1 g c) = level c
  ind2_level : ∀ g c, level (ind2 g c) = level c
  ind3_level : ∀ n c, level c ≤ level (ind3 n c)

namespace Core

variable {Label : Type u} {Choice : Type v} [AddGroup Label]
  (core : Core Label Choice)

def Ind1Step (a b : Choice) : Prop :=
  ∃ g, core.ind1 g a = b

def Ind2Step (a b : Choice) : Prop :=
  ∃ g, core.ind2 g a = b

def Ind3Step (a b : Choice) : Prop :=
  ∃ n, core.ind3 n a = b

theorem ind1Step_refl (a : Choice) : Ind1Step core a a := by
  exact ⟨0, core.ind1_zero a⟩

theorem ind1Step_symm {a b : Choice} (h : Ind1Step core a b) :
    Ind1Step core b a := by
  rcases h with ⟨g, h⟩
  refine ⟨-g, ?_⟩
  rw [← h, core.ind1_inverse]

theorem ind1Step_trans {a b c : Choice}
    (h₁ : Ind1Step core a b) (h₂ : Ind1Step core b c) :
    Ind1Step core a c := by
  rcases h₁ with ⟨g, rfl⟩
  rcases h₂ with ⟨h, rfl⟩
  exact ⟨g + h, core.ind1_add g h a⟩

theorem ind2Step_refl (a : Choice) : Ind2Step core a a := by
  exact ⟨0, core.ind2_zero a⟩

theorem ind2Step_symm {a b : Choice} (h : Ind2Step core a b) :
    Ind2Step core b a := by
  rcases h with ⟨g, h⟩
  refine ⟨-g, ?_⟩
  rw [← h, core.ind2_inverse]

theorem ind2Step_trans {a b c : Choice}
    (h₁ : Ind2Step core a b) (h₂ : Ind2Step core b c) :
    Ind2Step core a c := by
  rcases h₁ with ⟨g, rfl⟩
  rcases h₂ with ⟨h, rfl⟩
  exact ⟨g + h, core.ind2_add g h a⟩

theorem ind3Step_refl (a : Choice) : Ind3Step core a a := by
  exact ⟨0, core.ind3_zero a⟩

theorem ind3Step_trans {a b c : Choice}
    (h₁ : Ind3Step core a b) (h₂ : Ind3Step core b c) :
    Ind3Step core a c := by
  rcases h₁ with ⟨m, rfl⟩
  rcases h₂ with ⟨n, rfl⟩
  exact ⟨m + n, core.ind3_add m n a⟩

theorem ind1_preserves_level {a b : Choice}
    (h : Ind1Step core a b) : core.level a = core.level b := by
  rcases h with ⟨g, rfl⟩
  exact (core.ind1_level g a).symm

theorem ind2_preserves_level {a b : Choice}
    (h : Ind2Step core a b) : core.level a = core.level b := by
  rcases h with ⟨g, rfl⟩
  exact (core.ind2_level g a).symm

inductive GeneratedEqualityRelation : Choice → Choice → Prop
  | refl (a) : GeneratedEqualityRelation a a
  | ind1 {a b} : Ind1Step core a b → GeneratedEqualityRelation a b
  | ind2 {a b} : Ind2Step core a b → GeneratedEqualityRelation a b
  | symm {a b} : GeneratedEqualityRelation a b → GeneratedEqualityRelation b a
  | trans {a b c} : GeneratedEqualityRelation a b →
      GeneratedEqualityRelation b c → GeneratedEqualityRelation a c

theorem generatedRelation_refl (a : Choice) :
    GeneratedEqualityRelation core a a :=
  GeneratedEqualityRelation.refl a

theorem generatedRelation_symm {a b : Choice}
    (h : GeneratedEqualityRelation core a b) :
    GeneratedEqualityRelation core b a :=
  GeneratedEqualityRelation.symm h

theorem generatedRelation_trans {a b c : Choice}
    (h₁ : GeneratedEqualityRelation core a b)
    (h₂ : GeneratedEqualityRelation core b c) :
    GeneratedEqualityRelation core a c :=
  GeneratedEqualityRelation.trans h₁ h₂

theorem generatedRelation_level_eq
    {a b : Choice} (h : GeneratedEqualityRelation core a b) :
    core.level a = core.level b := by
  induction h with
  | refl a => rfl
  | ind1 hstep => exact Core.ind1_preserves_level core hstep
  | ind2 hstep => exact Core.ind2_preserves_level core hstep
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

def generatedSetoid : Setoid Choice where
  r := GeneratedEqualityRelation core
  iseqv :=
    { refl := generatedRelation_refl core
      symm := generatedRelation_symm core
      trans := generatedRelation_trans core }

abbrev GeneratedQuotient := Quotient (generatedSetoid core)

def generatedQuotientMap (a : Choice) : GeneratedQuotient core :=
  Quotient.mk'' a

theorem generatedQuotientMap_eq_iff {a b : Choice} :
    generatedQuotientMap core a = generatedQuotientMap core b ↔
      GeneratedEqualityRelation core a b := by
  change (Quotient.mk'' a : Quotient (generatedSetoid core)) =
      Quotient.mk'' b ↔ GeneratedEqualityRelation core a b
  exact Quotient.eq''

theorem generatedQuotientMap_level_eq {a b : Choice}
    (h : generatedQuotientMap core a = generatedQuotientMap core b) :
    core.level a = core.level b :=
  generatedRelation_level_eq core ((generatedQuotientMap_eq_iff core).mp h)

theorem generatedQuotient_no_level_collapse {a b : Choice}
    (hlevel : core.level a ≠ core.level b) :
    generatedQuotientMap core a ≠ generatedQuotientMap core b := by
  intro h
  exact hlevel (generatedQuotientMap_level_eq core h)

theorem generatedQuotientMap_eq_of_generated
    {a b : Choice} (h : GeneratedEqualityRelation core a b) :
    generatedQuotientMap core a = generatedQuotientMap core b :=
  (generatedQuotientMap_eq_iff core).mpr h

theorem generatedQuotientMap_ne_of_level_ne {a b : Choice}
    (hlevel : core.level a ≠ core.level b) :
    generatedQuotientMap core a ≠ generatedQuotientMap core b :=
  generatedQuotient_no_level_collapse core hlevel

end Core

end MultiradialKernel

end LeanFormal.IUT
