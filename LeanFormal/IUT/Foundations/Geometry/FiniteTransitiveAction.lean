import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.Tactic

/-!
  A finite transitive group action as an L1 mathematical foundation.

  This is the ordinary finite-fiber/orbit language underlying many later
  covering constructions.  It is deliberately not called a Hodge theater,
  anabelioid, or a Frobenioid: those source objects require additional
  geometry and compatibility data that are tracked elsewhere as obligations.
-/

namespace LeanFormal.IUT

structure FiniteTransitiveAction (G X : Type*) [Group G] [MulAction G X]
    [Fintype G] [Fintype X] where
  transitive : ∀ x y : X, ∃ g : G, g • x = y

theorem FiniteTransitiveAction.card_mul_stabilizer
    {G X : Type*} [Group G] [MulAction G X]
    [Fintype G] [Fintype X]
    (action : FiniteTransitiveAction G X) (x : X) :
    Nat.card X * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  letI : MulAction.IsPretransitive G X := ⟨action.transitive⟩
  letI : Fintype (MulAction.orbit G x) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer G x) := Fintype.ofFinite _
  have hcard :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := G) x
  have horbit : Fintype.card (MulAction.orbit G x) = Fintype.card X := by
    have hequiv : MulAction.orbit G x ≃ (Set.univ : Set X) :=
      Equiv.setCongr (MulAction.orbit_eq_univ G x)
    simpa using Fintype.card_congr hequiv
  calc
    Nat.card X * Nat.card (MulAction.stabilizer G x) =
        Fintype.card X * Fintype.card (MulAction.stabilizer G x) := by
      simp only [Nat.card_eq_fintype_card]
    _ = Fintype.card (MulAction.orbit G x) *
        Fintype.card (MulAction.stabilizer G x) := by rw [horbit]
    _ = Fintype.card G := hcard
    _ = Nat.card G := by simp only [Nat.card_eq_fintype_card]

theorem FiniteTransitiveAction.card_stabilizer_dvd_group
    {G X : Type*} [Group G] [MulAction G X]
    [Fintype G] [Fintype X]
    (action : FiniteTransitiveAction G X) (x : X) :
    Nat.card (MulAction.stabilizer G x) ∣ Nat.card G := by
  have hcard := action.card_mul_stabilizer x
  refine ⟨Nat.card X, ?_⟩
  simpa [Nat.mul_comm] using hcard.symm

end LeanFormal.IUT
