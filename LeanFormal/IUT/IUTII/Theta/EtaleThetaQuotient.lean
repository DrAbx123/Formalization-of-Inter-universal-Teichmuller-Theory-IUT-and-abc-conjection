/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Audit.Status
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
  Algebraic lower-central quotients used before the etale theta realization.

  This is adapted from the source-facing quotient layer in the current
  `promachina/iut-lean` tree.  It deliberately starts with an arbitrary
  Mathlib group: the geometric fundamental group, profinite topology, and
  etale-cover realization are later obligations, not hidden assumptions here.
  The quotient and power-kernel maps are therefore genuine group-theoretic
  constructions rather than a replacement matrix or an empty carrier.
-/

namespace LeanFormal.IUT

universe u

open scoped commutatorElement

section LowerCentral

variable (G : Type u) [Group G]

abbrev thetaDerivedSubgroup : Subgroup G :=
  commutator G

def thetaCommutatorKernel : Subgroup G :=
  ⁅(⊤ : Subgroup G), thetaDerivedSubgroup G⁆

instance thetaCommutatorKernel_normal :
    (thetaCommutatorKernel G).Normal := by
  change ⁅(⊤ : Subgroup G), commutator G⁆.Normal
  infer_instance

abbrev ThetaQuotient :=
  G ⧸ thetaCommutatorKernel G

abbrev EllipticAbelianization :=
  G ⧸ thetaDerivedSubgroup G

theorem thetaCommutatorKernel_le_derivedSubgroup :
    thetaCommutatorKernel G ≤ thetaDerivedSubgroup G :=
  Subgroup.commutator_le_right _ _

def thetaToElliptic :
    ThetaQuotient G →* EllipticAbelianization G :=
  QuotientGroup.map
    (thetaCommutatorKernel G)
    (thetaDerivedSubgroup G)
    (MonoidHom.id G)
    (thetaCommutatorKernel_le_derivedSubgroup G)

theorem thetaToElliptic_mk (g : G) :
    thetaToElliptic G (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl

def thetaPowerKernel (l : Nat) : Subgroup (ThetaQuotient G) :=
  Subgroup.normalClosure {x | ∃ y : ThetaQuotient G, x = y ^ l}

instance thetaPowerKernel_normal (l : Nat) :
    (thetaPowerKernel G l).Normal :=
  Subgroup.normalClosure_normal

def ellipticPowerKernel (l : Nat) : Subgroup (EllipticAbelianization G) :=
  Subgroup.normalClosure
    {x | ∃ y : EllipticAbelianization G, x = y ^ l}

instance ellipticPowerKernel_normal (l : Nat) :
    (ellipticPowerKernel G l).Normal :=
  Subgroup.normalClosure_normal

abbrev ModLThetaQuotient (l : Nat) :=
  ThetaQuotient G ⧸ thetaPowerKernel G l

abbrev ModLEllipticAbelianization (l : Nat) :=
  EllipticAbelianization G ⧸ ellipticPowerKernel G l

def modLThetaProjection (l : Nat) :
    G →* ModLThetaQuotient G l :=
  (QuotientGroup.mk' (thetaPowerKernel G l)).comp
    (QuotientGroup.mk' (thetaCommutatorKernel G))

def modLEllipticProjection (l : Nat) :
    G →* ModLEllipticAbelianization G l :=
  (QuotientGroup.mk' (ellipticPowerKernel G l)).comp
    (QuotientGroup.mk' (thetaDerivedSubgroup G))

theorem modLThetaProjection_surjective (l : Nat) :
    Function.Surjective (modLThetaProjection G l) :=
  (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)

theorem modLEllipticProjection_surjective (l : Nat) :
    Function.Surjective (modLEllipticProjection G l) :=
  (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)

theorem thetaToElliptic_maps_powerKernel (l : Nat) :
    thetaPowerKernel G l ≤
      (ellipticPowerKernel G l).comap (thetaToElliptic G) := by
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨y, rfl⟩
  change thetaToElliptic G (y ^ l) ∈ ellipticPowerKernel G l
  rw [map_pow]
  exact Subgroup.subset_normalClosure
    ⟨thetaToElliptic G y, rfl⟩

def modLThetaToElliptic (l : Nat) :
    ModLThetaQuotient G l →* ModLEllipticAbelianization G l :=
  QuotientGroup.map
    (thetaPowerKernel G l)
    (ellipticPowerKernel G l)
    (thetaToElliptic G)
    (thetaToElliptic_maps_powerKernel G l)

@[simp]
theorem modLThetaToElliptic_mk (l : Nat) (x : ThetaQuotient G) :
    modLThetaToElliptic G l (QuotientGroup.mk x) =
      QuotientGroup.mk (thetaToElliptic G x) :=
  rfl

theorem thetaToElliptic_surjective :
    Function.Surjective (thetaToElliptic G) := by
  intro x
  refine QuotientGroup.induction_on x ?_
  intro g
  exact ⟨QuotientGroup.mk g, rfl⟩

theorem modLThetaToElliptic_surjective (l : Nat) :
    Function.Surjective (modLThetaToElliptic G l) := by
  intro x
  refine QuotientGroup.induction_on x ?_
  intro y
  obtain ⟨z, rfl⟩ := thetaToElliptic_surjective G y
  exact ⟨QuotientGroup.mk z, rfl⟩

def thetaCenter : Subgroup (ThetaQuotient G) :=
  (thetaToElliptic G).ker

instance thetaCenter_normal : (thetaCenter G).Normal := by
  change (thetaToElliptic G).ker.Normal
  infer_instance

theorem thetaCenter_le_center :
    thetaCenter G ≤ Subgroup.center (ThetaQuotient G) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (thetaCommutatorKernel G) z
  have hg : g ∈ thetaDerivedSubgroup G := by
    apply (QuotientGroup.eq_one_iff g).mp
    exact hz
  intro q
  refine QuotientGroup.induction_on q ?_
  intro h
  apply commutatorElement_eq_one_iff_mul_comm.mp
  change QuotientGroup.mk' (thetaCommutatorKernel G) ⁅h, g⁆ = 1
  apply (QuotientGroup.eq_one_iff (⁅h, g⁆ : G)).mpr
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top h) hg

instance thetaCenter_isMulCommutative :
    IsMulCommutative (thetaCenter G) where
  is_comm := ⟨by
    intro first second
    apply Subtype.ext
    exact
      (Subgroup.mem_center_iff.mp
        (thetaCenter_le_center G first.2) second.1).symm⟩

end LowerCentral

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def etaleThetaQuotient : Obligation :=
  { id := "IUT-II.etale-theta-lower-central-quotients"
    source := "IUT II, Section 2; current promachina/iut-lean EtaleThetaQuotient"
    status := VerificationStatus.proved
    note :=
      "Mathlib commutator, normal-closure, quotient-group, power-kernel, " ++
        "surjection, and central-kernel constructions are proved. The " ++
        "arithmetic etale fundamental group, profinite closedness, and " ++
        "rank-two (Z/lZ)^2 identification remain source obligations."
    dependsOn := [ "IUT-I.initial-theta-arithmetic-data" ] }

end LeanFormal.IUT.Audit
