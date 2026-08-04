import LeanFormal.IUT.IUTII.Frobenioid.LocalTorsionCyclotome
import LeanFormal.IUT.IUTII.Kummer.LocalGaloisKummerAction
import LeanFormal.IUT.IUTII.Kummer.TimesMuIsm

/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

/-!
  A literal local MLF `TM` model over `Q_p`.

  Absolute Anabelian Topics III, Definition 3.1(i)-(ii), uses a topological
  group `Pi_k`, a continuous surjection to the absolute Galois group, and the
  induced action on the torsion-cyclotomic arithmetic monoid.  Here the
  arithmetic monoid is the actual nonzero integral closure already constructed
  in `LocalIntegralMonoid.lean`; its torsion-cyclotomic structure is proved in
  `LocalTorsionCyclotome.lean`.

  The canonical mono-analytic model takes `Pi_k = G_k` and the identity
  augmentation.  The more general record below retains exactly the continuous
  augmentation needed to pull Krull-open stabilizers back to `Pi_k`; it does
  not assert that arbitrary such records exist.
-/

namespace LeanFormal.IUT

structure LocalMLFModelTMPair
    (p : Nat) [Fact (Nat.Prime p)] where
  actingGroup : Type
  [groupStructure : Group actingGroup]
  [topology : TopologicalSpace actingGroup]
  [topologicalGroup : IsTopologicalGroup actingGroup]
  augmentation : actingGroup →ₜ* LocalAbsoluteGalois p
  augmentation_surjective : Function.Surjective augmentation

attribute [instance]
  LocalMLFModelTMPair.groupStructure
  LocalMLFModelTMPair.topology
  LocalMLFModelTMPair.topologicalGroup

namespace LocalMLFModelTMPair

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The arithmetic-monoid action induced by the Galois augmentation. -/
noncomputable def action (pair : LocalMLFModelTMPair p) :
    pair.actingGroup →* MulAut (LocalIntegralMonoid p) :=
  (LocalIntegralMonoid.galoisAction p).comp
    pair.augmentation.toMonoidHom

/-- The induced action on integral-monoid units. -/
noncomputable def unitAction (pair : LocalMLFModelTMPair p) :
    pair.actingGroup →* MulAut (LocalIntegralMonoid p)ˣ :=
  (LocalIntegralMonoid.unitAction p).comp
    pair.augmentation.toMonoidHom

/-- The action on `O^{times-mu}` obtained by quotienting all torsion units. -/
noncomputable def timesMuAction (pair : LocalMLFModelTMPair p) :
    pair.actingGroup →*
      MulAut (TimesMuQuotient (LocalIntegralMonoid p)ˣ) :=
  TimesMuQuotient.action (pair.unitAction p)

/-- Pull the Krull-open stabilizer of a model element back along `Pi_k -> G_k`. -/
noncomputable def openStabilizer
    (pair : LocalMLFModelTMPair p)
    (value : LocalIntegralMonoid p) :
    OpenSubgroup pair.actingGroup :=
  (LocalIntegralMonoid.openStabilizer p value).comap
    pair.augmentation.toMonoidHom
    pair.augmentation.continuous_toFun

theorem openStabilizer_fixed
    (pair : LocalMLFModelTMPair p)
    (value : LocalIntegralMonoid p)
    (g : pair.openStabilizer p value) :
    pair.action p (g : pair.actingGroup) value = value := by
  exact LocalIntegralMonoid.openStabilizer_fixed p value
    ⟨pair.augmentation (g : pair.actingGroup), g.property⟩

/-- The mono-analytic model: the absolute Galois group with identity
augmentation. -/
noncomputable def monoAnalytic : LocalMLFModelTMPair p where
  actingGroup := LocalAbsoluteGalois p
  groupStructure := inferInstance
  topology := inferInstance
  topologicalGroup := inferInstance
  augmentation := ContinuousMonoidHom.id _
  augmentation_surjective := Function.surjective_id

@[simp]
theorem monoAnalytic_augmentation_apply (g : LocalAbsoluteGalois p) :
    (monoAnalytic p).augmentation g = g :=
  rfl

@[simp]
theorem monoAnalytic_action_apply
    (g : LocalAbsoluteGalois p) (value : LocalIntegralMonoid p) :
    (monoAnalytic p).action p g value =
      LocalIntegralMonoid.galoisAction p g value :=
  rfl

@[simp]
theorem monoAnalytic_unitAction_apply
    (g : LocalAbsoluteGalois p) (value : (LocalIntegralMonoid p)ˣ) :
    (monoAnalytic p).unitAction p g value =
      LocalIntegralMonoid.unitAction p g value :=
  rfl

@[simp]
theorem monoAnalytic_timesMuAction_quotientMap
    (g : LocalAbsoluteGalois p) (value : (LocalIntegralMonoid p)ˣ) :
    (monoAnalytic p).timesMuAction p g
        (TimesMuQuotient.quotientMap value) =
      TimesMuQuotient.quotientMap
        (LocalIntegralMonoid.unitAction p g value) :=
  rfl

/-- The actual mono-analytic action instantiates the previously proved
`times-mu` Kummer-isomorphism kernel.  This is only the identity representative;
it does not assert a Frobenioid-side comparison. -/
noncomputable def monoAnalyticTimesMuIdentity :
    TimesMuKummer.Isomorphism
      ((monoAnalytic p).unitAction p)
      ((monoAnalytic p).unitAction p) :=
  TimesMuKummer.Isomorphism.refl ((monoAnalytic p).unitAction p)

end LocalMLFModelTMPair

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def localMLFModelTMPair : Obligation :=
  { id := "IUT-II.local-MLF-TM-pair"
    source := "Absolute Anabelian Topics III, Definition 3.1(i)-(ii); IUT II local Kummer input"
    status := VerificationStatus.proved
    note :=
      "The canonical mono-analytic local model uses the Krull-topological " ++
        "absolute Galois group of Q_p, the continuous identity augmentation, " ++
        "the actual nonzero integral-closure monoid, and its proved " ++
        "torsion-cyclotomic structure. The induced monoid, unit, and times-mu " ++
        "actions are constructed. Pullbacks of the genuine Krull-open " ++
        "stabilizers are proved to fix their elements. The identity times-mu " ++
        "Kummer representative is constructed, but no group/Frobenioid " ++
        "comparison is claimed."
    dependsOn :=
      [ "IUT-II.local-torsion-cyclotome",
        "IUT-II.local-discrete-galois-kummer-action",
        "IUT-II.times-mu-ism-orbit" ] }

end LeanFormal.IUT.Audit
