/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.ResiduallyFinite
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype

/-!
# Finite permutation separation of a reduced word

A nonempty reduced word can be detected by permutations of a finite set.  The
construction reserves one state for every prefix and extends the partial
permutation prescribed by each generator.  Reducedness is exactly what makes
the prescribed sources and targets injective.
-/

namespace Iut

universe u v

namespace SourceReducedWordFiniteSeparation

variable {Generator : Type u} (word : List (Generator × Bool))

abbrev Position := Fin word.length

abbrev State := Fin (word.length + 1)

def before (position : Position word) : State word :=
  ⟨position.1, Nat.lt_succ_of_lt position.2⟩

def after (position : Position word) : State word :=
  ⟨position.1 + 1, Nat.add_lt_add_right position.2 1⟩

def letter (position : Position word) : Generator × Bool :=
  word.get position

abbrev Occurrence (generator : Generator) :=
  {position : Position word // (letter word position).1 = generator}

def source (generator : Generator) (occurrence : Occurrence word generator) :
    State word :=
  if (letter word occurrence.1).2 then before word occurrence.1
  else after word occurrence.1

def target (generator : Generator) (occurrence : Occurrence word generator) :
    State word :=
  if (letter word occurrence.1).2 then after word occurrence.1
  else before word occurrence.1

private theorem adjacent_sign_eq
    (reduced : FreeGroup.IsReduced word)
    (first second : Position word)
    (successive : first.1 + 1 = second.1)
    (sameGenerator : (letter word first).1 = (letter word second).1) :
    (letter word first).2 = (letter word second).2 := by
  rw [FreeGroup.IsReduced, List.isChain_iff_getElem] at reduced
  have adjacent := reduced first.1 (by omega)
  have firstGet : word[first.1] = letter word first := by
    simp [letter]
  have secondGet : word[first.1 + 1] = letter word second := by
    simp [letter, successive]
  rw [firstGet, secondGet] at adjacent
  exact adjacent sameGenerator

theorem source_injective (reduced : FreeGroup.IsReduced word)
    (generator : Generator) :
    Function.Injective (source word generator) := by
  intro first second equality
  apply Subtype.ext
  apply Fin.ext
  have valueEquality := congrArg Fin.val equality
  by_cases firstPositive : (letter word first.1).2 = true
  · by_cases secondPositive : (letter word second.1).2 = true
    · simp [source, firstPositive, secondPositive, before]
        at valueEquality
      omega
    · simp [source, firstPositive, secondPositive, before, after]
        at valueEquality
      have successive : second.1.1 + 1 = first.1.1 := by omega
      have sameGenerator :
          (letter word second.1).1 = (letter word first.1).1 :=
        second.2.trans first.2.symm
      have signs := adjacent_sign_eq word reduced second.1 first.1
        successive sameGenerator
      exact (secondPositive (signs.trans firstPositive)).elim
  · by_cases secondPositive : (letter word second.1).2 = true
    · simp [source, firstPositive, secondPositive, before, after]
        at valueEquality
      have successive : first.1.1 + 1 = second.1.1 := by omega
      have sameGenerator :
          (letter word first.1).1 = (letter word second.1).1 :=
        first.2.trans second.2.symm
      have signs := adjacent_sign_eq word reduced first.1 second.1
        successive sameGenerator
      exact (firstPositive (signs.trans secondPositive)).elim
    · simp [source, firstPositive, secondPositive, after]
        at valueEquality
      omega

theorem target_injective (reduced : FreeGroup.IsReduced word)
    (generator : Generator) :
    Function.Injective (target word generator) := by
  intro first second equality
  apply Subtype.ext
  apply Fin.ext
  have valueEquality := congrArg Fin.val equality
  by_cases firstPositive : (letter word first.1).2 = true
  · by_cases secondPositive : (letter word second.1).2 = true
    · simp [target, firstPositive, secondPositive, after]
        at valueEquality
      omega
    · simp [target, firstPositive, secondPositive, before, after]
        at valueEquality
      have successive : first.1.1 + 1 = second.1.1 := by omega
      have sameGenerator :
          (letter word first.1).1 = (letter word second.1).1 :=
        first.2.trans second.2.symm
      have signs := adjacent_sign_eq word reduced first.1 second.1
        successive sameGenerator
      exact (secondPositive (signs.symm.trans firstPositive)).elim
  · by_cases secondPositive : (letter word second.1).2 = true
    · simp [target, firstPositive, secondPositive, before, after]
        at valueEquality
      have successive : second.1.1 + 1 = first.1.1 := by omega
      have sameGenerator :
          (letter word second.1).1 = (letter word first.1).1 :=
        second.2.trans first.2.symm
      have signs := adjacent_sign_eq word reduced second.1 first.1
        successive sameGenerator
      exact (firstPositive (signs.symm.trans secondPositive)).elim
    · simp [target, firstPositive, secondPositive, before]
        at valueEquality
      omega

/-- Extend the prefix transitions belonging to one generator to a permutation
of the complete finite state set. -/
noncomputable def generatorPerm (reduced : FreeGroup.IsReduced word)
    (generator : Generator) : Equiv.Perm (State word) :=
  Classical.choose <| Equiv.Perm.exists_extending_pair
    (source word generator) (target word generator)
    (source_injective word reduced generator)
    (target_injective word reduced generator)

theorem generatorPerm_occurrence (reduced : FreeGroup.IsReduced word)
    (generator : Generator) (occurrence : Occurrence word generator) :
    generatorPerm word reduced generator (source word generator occurrence) =
      target word generator occurrence :=
  by
    change (Classical.choose <| Equiv.Perm.exists_extending_pair
      (source word generator) (target word generator)
      (source_injective word reduced generator)
      (target_injective word reduced generator))
        (source word generator occurrence) = target word generator occurrence
    exact (Classical.choose_spec <| Equiv.Perm.exists_extending_pair
      (source word generator) (target word generator)
      (source_injective word reduced generator)
      (target_injective word reduced generator)) occurrence

/-- The signed action of one word letter. -/
noncomputable def letterPerm (reduced : FreeGroup.IsReduced word)
    (value : Generator × Bool) : Equiv.Perm (State word) :=
  if value.2 then generatorPerm word reduced value.1
  else (generatorPerm word reduced value.1).symm

/-- At every position, the signed letter permutation advances from the state
of the preceding prefix to the state of the succeeding prefix. -/
theorem letterPerm_letter (reduced : FreeGroup.IsReduced word)
    (position : Position word) :
    letterPerm word reduced (letter word position) (before word position) =
      after word position := by
  let occurrence : Occurrence word (letter word position).1 := ⟨position, rfl⟩
  have extension := generatorPerm_occurrence word reduced
    (letter word position).1 occurrence
  by_cases positive : (letter word position).2 = true
  · simpa [letterPerm, source, target, positive, occurrence] using extension
  · rw [show letterPerm word reduced (letter word position) =
        (generatorPerm word reduced (letter word position).1).symm by
      simp [letterPerm, positive]]
    have forward :
        generatorPerm word reduced (letter word position).1
            (after word position) = before word position := by
      simpa [source, target, positive, occurrence] using extension
    exact (generatorPerm word reduced
      (letter word position).1).symm_apply_eq.mpr forward.symm

/-- The state representing a prefix of the displayed length. -/
def prefixState (length : ℕ) (bounded : length ≤ word.length) : State word :=
  ⟨length, Nat.lt_succ_iff.mpr bounded⟩

/-- Running the first `length` letters reaches precisely the corresponding
prefix state. -/
theorem foldl_take_eq_prefixState (reduced : FreeGroup.IsReduced word) :
    ∀ (length : ℕ) (bounded : length ≤ word.length),
      (word.take length).foldl
          (fun state value ↦ letterPerm word reduced value state)
          (prefixState word 0 (Nat.zero_le _)) =
        prefixState word length bounded := by
  intro length
  induction length with
  | zero =>
      intro bounded
      rfl
  | succ length inductionHypothesis =>
      intro bounded
      have positionBound : length < word.length := by omega
      rw [← List.take_concat_get positionBound, List.concat_eq_append]
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [inductionHypothesis positionBound.le]
      let position : Position word := ⟨length, positionBound⟩
      have advances := letterPerm_letter word reduced position
      simpa [position, letter, before, after, prefixState] using advances

/-- Sequentially evaluate the complete reduced word on its initial state. -/
noncomputable def run (reduced : FreeGroup.IsReduced word) : State word :=
  word.foldl (fun state value ↦ letterPerm word reduced value state)
    (prefixState word 0 (Nat.zero_le _))

theorem run_eq_finalState (reduced : FreeGroup.IsReduced word) :
    run word reduced = prefixState word word.length (le_refl _) := by
  have complete := foldl_take_eq_prefixState word reduced
    word.length (le_refl _)
  simpa [run] using complete

/-- A nonempty reduced word moves the initial prefix state. -/
theorem run_ne_initial (reduced : FreeGroup.IsReduced word)
    (nonempty : word ≠ []) :
    run word reduced ≠ prefixState word 0 (Nat.zero_le _) := by
  rw [run_eq_finalState word reduced]
  intro equality
  have values := congrArg Fin.val equality
  simp only [prefixState] at values
  have positive : 0 < word.length := List.length_pos_of_ne_nil nonempty
  omega

section FreeGroup

variable (assignment : Generator → Equiv.Perm (State word))

private noncomputable def oppositeGenerator :
    Generator → (Equiv.Perm (State word))ᵐᵒᵖ :=
  fun generator ↦ MulOpposite.op (assignment generator)

private theorem unop_signed_prod_apply
    {StateType : Type v} (letters : List (Generator × Bool))
    (permutation : Generator → Equiv.Perm StateType) (initial : StateType) :
    MulOpposite.unop
        (List.prod (letters.map fun value ↦
          if value.2 then MulOpposite.op (permutation value.1)
          else (MulOpposite.op (permutation value.1))⁻¹)) initial =
      letters.foldl (fun state value ↦
        (if value.2 then permutation value.1 else (permutation value.1)⁻¹)
          state) initial := by
  induction letters generalizing initial with
  | nil => simp
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.prod_cons, List.foldl_cons,
        MulOpposite.unop_mul]
      rw [show MulOpposite.unop
          (if value.2 then MulOpposite.op (permutation value.1)
            else (MulOpposite.op (permutation value.1))⁻¹) =
          (if value.2 then permutation value.1 else (permutation value.1)⁻¹) by
        split <;> simp]
      exact inductionHypothesis _

private theorem unop_lift_mk_apply
    (initial : State word) :
    MulOpposite.unop
        (FreeGroup.lift (oppositeGenerator word assignment)
          (FreeGroup.mk word)) initial =
      word.foldl (fun state value ↦
        (if value.2 then assignment value.1 else (assignment value.1)⁻¹)
          state) initial := by
  rw [FreeGroup.lift_mk]
  simpa only [oppositeGenerator, cond_eq_ite] using
    unop_signed_prod_apply word assignment initial

/-- The homomorphism to a finite permutation group selected by the reduced
normal form of a free-group element. -/
noncomputable def freeGroupSeparatingHom (reduced : FreeGroup.IsReduced word) :
    FreeGroup Generator →* (Equiv.Perm (State word))ᵐᵒᵖ :=
  FreeGroup.lift (oppositeGenerator word (generatorPerm word reduced))

theorem freeGroupSeparatingHom_mk_ne_one
    (reduced : FreeGroup.IsReduced word) (nonempty : word ≠ []) :
    freeGroupSeparatingHom word reduced (FreeGroup.mk word) ≠ 1 := by
  intro equality
  have atInitial := congrArg
    (fun permutation : (Equiv.Perm (State word))ᵐᵒᵖ ↦
      MulOpposite.unop permutation (prefixState word 0 (Nat.zero_le _)))
    equality
  change MulOpposite.unop
      (FreeGroup.lift
        (oppositeGenerator word (generatorPerm word reduced))
        (FreeGroup.mk word))
      (prefixState word 0 (Nat.zero_le _)) =
    prefixState word 0 (Nat.zero_le _) at atInitial
  rw [unop_lift_mk_apply] at atInitial
  change run word reduced = prefixState word 0 (Nat.zero_le _) at atInitial
  exact run_ne_initial word reduced nonempty atInitial

/-- Free groups are residually finite, with an explicit prefix-permutation
quotient for each nontrivial reduced word. -/
noncomputable instance freeGroup_residuallyFinite :
    Group.ResiduallyFinite (FreeGroup Generator) := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro value nontrivial
  let word := value.toWord
  have reduced : FreeGroup.IsReduced word := by
    simpa [word] using FreeGroup.isReduced_toWord (x := value)
  have nonempty : word ≠ [] := by
    intro empty
    apply nontrivial
    calc
      value = FreeGroup.mk word := FreeGroup.mk_toWord.symm
      _ = FreeGroup.mk [] := congrArg FreeGroup.mk empty
      _ = 1 := FreeGroup.one_eq_mk.symm
  letI : Finite (Equiv.Perm (State word)) := inferInstance
  letI : Finite (Equiv.Perm (State word))ᵐᵒᵖ :=
    Finite.of_equiv (Equiv.Perm (State word)) MulOpposite.opEquiv
  exact ⟨(Equiv.Perm (State word))ᵐᵒᵖ, inferInstance, inferInstance,
    freeGroupSeparatingHom word reduced, by
      rw [← FreeGroup.mk_toWord (x := value)]
      exact freeGroupSeparatingHom_mk_ne_one word reduced nonempty⟩

end FreeGroup

end SourceReducedWordFiniteSeparation

/-- Residual finiteness transports from a free basis to every free group. -/
theorem IsFreeGroup.residuallyFinite
    (G : Type u) [Group G] [IsFreeGroup G] : Group.ResiduallyFinite G := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro value nontrivial
  let representation := IsFreeGroup.toFreeGroup G
  have representedNontrivial : representation value ≠ 1 := by
    intro equality
    apply nontrivial
    exact representation.injective (by simpa using equality)
  letI : Group.ResiduallyFinite
      (FreeGroup (IsFreeGroup.Generators G)) :=
    SourceReducedWordFiniteSeparation.freeGroup_residuallyFinite
  obtain ⟨normal, notMem⟩ :=
    Group.exists_finiteIndexNormalSubgroup_notMem
      (representation value) representedNontrivial
  exact ⟨FreeGroup (IsFreeGroup.Generators G) ⧸ normal.toSubgroup,
    inferInstance, inferInstance,
    (QuotientGroup.mk' normal.toSubgroup).comp representation.toMonoidHom,
    by simpa [QuotientGroup.eq_one_iff] using notMem⟩

end Iut
