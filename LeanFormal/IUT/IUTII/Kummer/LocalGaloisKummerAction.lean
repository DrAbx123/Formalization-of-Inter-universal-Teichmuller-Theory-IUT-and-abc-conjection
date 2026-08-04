import LeanFormal.IUT.IUTII.Kummer.CanonicalKummerMap
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.Padics.PadicNumbers

/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
  The local absolute-Galois specialization of the group-side Kummer map.

  The coefficient units are deliberately given the discrete algebraic-unit
  topology.  Mathlib's Krull-topology theorem then proves that the stabilizer
  of every algebraic unit is open, which gives joint continuity of the action.
  This is the discrete coefficient model used by the continuous-germ layer;
  the source's ind-topological integral monoid and its Frobenioid evaluation
  remain separate constructions.
-/

namespace LeanFormal.IUT

universe u

namespace LocalGaloisKummerAction

noncomputable section

variable (p : Nat) [Fact (Nat.Prime p)]

local instance unitsTopology :
    TopologicalSpace ((AlgebraicClosure ℚ_[p])ˣ) := ⊥

local instance unitsDiscreteTopology :
    DiscreteTopology ((AlgebraicClosure ℚ_[p])ˣ) :=
  discreteTopology_bot _

local instance unitsMulAction :
    MulAction (LocalAbsoluteGalois p) ((AlgebraicClosure ℚ_[p])ˣ) :=
  MulAction.compHom _ (localGaloisUnitsAction p)

theorem units_stabilizer_eq_field_stabilizer
    (u : (AlgebraicClosure ℚ_[p])ˣ) :
    (MulAction.stabilizer (LocalAbsoluteGalois p) u : Set (LocalAbsoluteGalois p)) =
      (MulAction.stabilizer (LocalAbsoluteGalois p)
        (u : AlgebraicClosure ℚ_[p]) : Set (LocalAbsoluteGalois p)) := by
  ext sigma
  constructor
  · intro h
    change localGaloisUnitsAction p sigma u = u at h
    exact congrArg Units.val h
  · intro h
    change localGaloisUnitsAction p sigma u = u
    apply Units.ext
    exact h

theorem continuous_units_smul :
    ContinuousSMul (LocalAbsoluteGalois p) ((AlgebraicClosure ℚ_[p])ˣ) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro u
  rw [units_stabilizer_eq_field_stabilizer p u]
  exact stabilizer_isOpen_of_isIntegral (K := ℚ_[p])
    (L := AlgebraicClosure ℚ_[p]) (u : AlgebraicClosure ℚ_[p])

noncomputable def action :
    DiscreteContinuousGroupAction (LocalAbsoluteGalois p)
      ((AlgebraicClosure ℚ_[p])ˣ) where
  automorphism := localGaloisUnitsAction p
  continuous_action := by
    exact (continuous_units_smul p).continuous_smul

noncomputable def germHom :
    (AlgebraicClosure ℚ_[p])ˣ →*
      Iut.ContinuousH1Germ
        (KummerCyclotome.continuousAction (action p)) := by
  letI : RootableBy ((AlgebraicClosure ℚ_[p])ˣ) ℕ :=
    AlgebraicClosureRootSystem.unitsRootableByNat
  exact CanonicalKummerMap.hom (action p)

end

end LocalGaloisKummerAction

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localDiscreteGaloisKummerAction : Obligation :=
  { id := "IUT-II.local-discrete-galois-kummer-action"
    source := "IUT II, Example 1.8(ii)-(iv); Mathlib Krull topology theorem"
    status := VerificationStatus.proved
    note :=
      "For the algebraic closure of Q_p with the explicitly declared discrete " ++
        "unit coefficient topology, the stabilizer of every unit is identified " ++
        "with the field stabilizer and is proved open by the integral-extension " ++
        "Krull-topology theorem. This yields a genuine continuous action and a " ++
        "group-side Kummer germ homomorphism. It is not the source's ind-topological " ++
        "integral monoid or Frobenioid evaluation."
    dependsOn := ["IUT-II.canonical-continuous-kummer-map",
      "IUT-I-II.local-prime-place-carrier"] }

end LeanFormal.IUT.Audit
