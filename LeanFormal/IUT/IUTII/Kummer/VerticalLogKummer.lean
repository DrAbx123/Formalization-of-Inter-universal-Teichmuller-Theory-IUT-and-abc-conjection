/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Kummer.KummerRootRatio

/-!
  The source-facing vertical log-Kummer correspondence contract.

  This record uses ordered source and target layers and states the upper-semi
  inclusion (Ind3) at the level of Kummer images.  It is a contract for the
  actual Frobenioid/log-shell construction, not a proof that arbitrary types
  carry such a correspondence.  The concrete construction is pending.
-/

namespace LeanFormal.IUT

set_option linter.checkUnivs false in
structure VerticalLogKummerCorrespondence where
  D : Type*
  [ordD : Preorder D]
  F : Nat → Type*
  [ordF : ∀ m, Preorder (F m)]
  log : ∀ m, F m → F (m + 1)
  kummer : ∀ m, F m → D
  upperSemi : ∀ (m : Nat) (x : F m), kummer m x ≤ kummer (m + 1) (log m x)

attribute [instance] VerticalLogKummerCorrespondence.ordD
  VerticalLogKummerCorrespondence.ordF

namespace VerticalLogKummerCorrespondence

variable (K : VerticalLogKummerCorrespondence)

def transport (m : Nat) : (n : Nat) → K.F m → K.F (m + n)
  | 0 => id
  | n + 1 => fun x => K.log (m + n) (transport m n x)

@[simp] theorem transport_zero (m : Nat) (x : K.F m) :
    K.transport m 0 x = x := rfl

theorem kummer_le_transport (m : Nat) (x : K.F m) :
    ∀ n : Nat, K.kummer m x ≤ K.kummer (m + n) (K.transport m n x)
  | 0 => le_refl _
  | n + 1 =>
      (kummer_le_transport m x n).trans
        (K.upperSemi (m + n) (K.transport m n x))

def HullDominates (x₀ : K.F 0) (hull : K.D) : Prop :=
  ∀ n : Nat, K.kummer (0 + n) (K.transport 0 n x₀) ≤ hull

theorem base_le_hull {x₀ : K.F 0} {hull : K.D}
    (h : K.HullDominates x₀ hull) : K.kummer 0 x₀ ≤ hull := by
  simpa using h 0

end VerticalLogKummerCorrespondence

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def verticalLogKummer : Obligation :=
  { id := "IUT-II.vertical-log-kummer-correspondence"
    source := "IUT II, Sections 5--6; IUT III, Proposition 3.5 and Theorem 3.11(ii)"
    status := VerificationStatus.interface
    note :=
      "The source-facing ordered-layer contract, transport iteration, and " ++
        "upper-semi image inclusion are formalized. The actual log-shell, " ++
        "Frobenioid, local/global Kummer maps, and arithmetic construction are " ++
        "not assumed and remain pending."
    dependsOn := [ "IUT-II.kummer-root-ratio-contract",
      "IUT-I-II.prime-strips-frobenioids" ] }

end LeanFormal.IUT.Audit
