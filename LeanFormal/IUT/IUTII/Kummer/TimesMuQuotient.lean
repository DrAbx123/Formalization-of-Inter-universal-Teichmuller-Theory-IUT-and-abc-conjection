/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.IUTII.Frobenioid.LocalPrimeStrip
import Mathlib.GroupTheory.Torsion

namespace LeanFormal.IUT

/-!
  The algebraic quotient by roots of unity from IUT II, Definition 4.9(i).

  For a commutative group `U`, `TimesMuQuotient U` is `U` modulo its full
  torsion subgroup.  Every multiplicative automorphism preserves that subgroup,
  so an action on `U` descends to the quotient.  This file proves the quotient
  map's kernel and surjectivity, the descended action laws and equivariance, and
  torsion-freeness of the quotient.

  The ind-topology, the group-theoretic `O^xmu(G)`, Ism-orbits of Kummer
  isomorphisms, and the open-subgroup invariant modules of Definition 4.9(i)
  are separate constructions.
-/

universe u v

abbrev TimesMuQuotient (U : Type u) [CommGroup U] : Type u :=
  U ⧸ CommGroup.torsion U

namespace TimesMuQuotient

variable {G : Type v} {U : Type u} [Group G] [CommGroup U]

def quotientMap : U →* TimesMuQuotient U :=
  QuotientGroup.mk' (CommGroup.torsion U)

@[simp] theorem quotientMap_apply (u : U) :
    quotientMap u = (u : TimesMuQuotient U) := rfl

theorem quotientMap_surjective : Function.Surjective (quotientMap (U := U)) :=
  QuotientGroup.mk'_surjective (CommGroup.torsion U)

theorem quotientMap_ker :
    MonoidHom.ker (quotientMap (U := U)) = CommGroup.torsion U :=
  by
    simpa only [quotientMap] using
      (QuotientGroup.ker_mk' (N := CommGroup.torsion U))

theorem torsion_preserved (e : MulAut U) :
    (CommGroup.torsion U).map e = CommGroup.torsion U :=
  e.map_torsion

def descendAut (e : MulAut U) : MulAut (TimesMuQuotient U) :=
  QuotientGroup.congr (CommGroup.torsion U) (CommGroup.torsion U) e e.map_torsion

@[simp] theorem descendAut_quotientMap (e : MulAut U) (u : U) :
    descendAut e (quotientMap u) = quotientMap (e u) := rfl

def action (rho : G →* MulAut U) : G →* MulAut (TimesMuQuotient U) where
  toFun g := descendAut (rho g)
  map_one' := by
    ext x
    obtain ⟨u, rfl⟩ := quotientMap_surjective (U := U) x
    rw [rho.map_one]
    change descendAut 1 (quotientMap u) = quotientMap u
    rw [descendAut_quotientMap]
    rfl
  map_mul' g h := by
    ext x
    obtain ⟨u, rfl⟩ := quotientMap_surjective (U := U) x
    rw [rho.map_mul]
    change descendAut (rho g * rho h) (quotientMap u) =
      descendAut (rho g) (descendAut (rho h) (quotientMap u))
    rw [descendAut_quotientMap, descendAut_quotientMap,
      descendAut_quotientMap]
    rfl

@[simp] theorem action_quotientMap (rho : G →* MulAut U) (g : G) (u : U) :
    action rho g (quotientMap u) = quotientMap (rho g u) := rfl

theorem action_one (rho : G →* MulAut U) (x : TimesMuQuotient U) :
    action rho 1 x = x := by
  rw [(action rho).map_one]
  rfl

theorem action_mul (rho : G →* MulAut U) (g h : G)
    (x : TimesMuQuotient U) :
    action rho (g * h) x = action rho g (action rho h x) := by
  rw [(action rho).map_mul]
  rfl

theorem torsion_eq_bot :
    CommGroup.torsion (TimesMuQuotient U) = ⊥ :=
  CommGroup.isMulTorsionFree_iff_torsion_eq_bot.mp inferInstance

end TimesMuQuotient

namespace FPrimeStrip

variable {V : Type*} (F : FPrimeStrip V) (v : V)

def unitsAction :
    F.toDPrimeStrip.Pi v →* MulAut (F.Mon v)ˣ where
  toFun g := Units.mapEquiv (F.action v g)
  map_one' := by
    ext u
    rw [(F.action v).map_one]
    rfl
  map_mul' g h := by
    ext u
    rw [(F.action v).map_mul]
    rfl

abbrev timesMuQuotient : Type _ := TimesMuQuotient (F.Mon v)ˣ

def timesMuAction :
    F.toDPrimeStrip.Pi v →* MulAut (F.timesMuQuotient v) :=
  TimesMuQuotient.action (F.unitsAction v)

@[simp] theorem unitsAction_val
    (g : F.toDPrimeStrip.Pi v) (u : (F.Mon v)ˣ) :
    ↑(F.unitsAction v g u) = F.action v g (↑u : F.Mon v) := rfl

@[simp] theorem timesMuAction_quotientMap
    (g : F.toDPrimeStrip.Pi v) (u : (F.Mon v)ˣ) :
    F.timesMuAction v g (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (F.unitsAction v g u) := rfl

end FPrimeStrip

noncomputable abbrev localTimesMuQuotient (v : RationalPrimePlace) : Type :=
  localFPrimeStrip.timesMuQuotient v

noncomputable def localTimesMuAction (v : RationalPrimePlace) :
    localFPrimeStrip.toDPrimeStrip.Pi v →* MulAut (localTimesMuQuotient v) :=
  localFPrimeStrip.timesMuAction v

@[simp] theorem localTimesMuAction_quotientMap
    (v : RationalPrimePlace) (g : localFPrimeStrip.toDPrimeStrip.Pi v)
    (u : (localFPrimeStrip.Mon v)ˣ) :
    localTimesMuAction v g (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (localFPrimeStrip.unitsAction v g u) := rfl

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def timesMuQuotient : Obligation :=
  { id := "IUT-II.times-mu-torsion-quotient"
    source := "IUT II, Definition 4.9(i)"
    status := VerificationStatus.proved
    note :=
      "The quotient of a commutative unit group by its full torsion subgroup, " ++
        "the quotient kernel and surjectivity, preservation of torsion by every " ++
        "automorphism, the descended G-action and equivariance, and torsion-freeness " ++
        "are proved. The ind-topological and Ism-orbit Kummer structures remain later."
    dependsOn := ["IUT-I-II.local-f-prime-strip-carrier"] }

end LeanFormal.IUT.Audit
