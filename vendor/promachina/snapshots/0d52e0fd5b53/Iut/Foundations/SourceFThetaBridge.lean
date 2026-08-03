/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceProcession

/-!
# Source F-theta bridges

This module formalizes the F-prime-strip portion of IUT I, Definition 5.5(ii).
An F-level poly-arrow is transported to a D-level poly-arrow by the functor of
Remark 5.2.1(i).  The uniqueness of lifts asserted in Definition 5.5(ii)(d)
is retained as an injectivity theorem obligation on the selected poly-arrows.
-/

open CategoryTheory

namespace Iut

universe u

/--
The F-prime-strip core of a theta bridge from IUT I, Definition 5.5(ii).

The target F-prime-strip is not an independent field: it is the strip
tautologically associated to the theta-Hodge theater.  The evaluation-label
bijection is the Proposition 4.7 output used by the associated D-theta bridge
and its procession.
-/
structure SourceFThetaBridge
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    (models : IUTIThetaHodgeTheaterModels theta) where
  capsule : SourceFPrimeStripCapsule models
  theater : SourceThetaHodgeTheater models
  capsule_history :
    ∀ j, (capsule.object j).history = theater.history
  polyMorphism :
    ∀ j, Set (capsule.object j ⟶ theater.associatedF)
  polyMorphism_nonempty :
    ∀ j, (polyMorphism j).Nonempty
  associatedD_injective :
    ∀ j
      (first second :
        capsule.object j ⟶ theater.associatedF),
      first ∈ polyMorphism j ->
      second ∈ polyMorphism j ->
      first.associatedD = second.associatedD ->
        first = second
  evaluationLabel :
    capsule.index ->
      EtaleTheta.SignLabel
        (EtaleTheta.LTorsionLabel theta.l.value)
  evaluationLabel_injective :
    Function.Injective evaluationLabel
  evaluationLabel_surjective :
    Function.Surjective evaluationLabel

namespace SourceFThetaBridge

variable
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod]
    [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K]
    [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : SourceInitialThetaCore Fmod F K}
    {models : IUTIThetaHodgeTheaterModels theta}

/--
The D-theta bridge associated to an F-theta bridge by Remark 5.2.1(i).

Its selected D-poly-arrows are exactly the images of the selected F-poly-arrows.
-/
def associatedD (bridge : SourceFThetaBridge models) :
    SourceDThetaBridgeCore models where
  capsule :=
    CategoryCapsule.map sourceFPrimeStripToD
      bridge.capsule
  target :=
    bridge.theater.associatedF.associatedD
  capsule_history j := bridge.capsule_history j
  polyMorphism j :=
    { arrow |
      ∃ lift :
          bridge.capsule.object j ⟶
            bridge.theater.associatedF,
        lift ∈ bridge.polyMorphism j ∧
          lift.associatedD = arrow }
  polyMorphism_nonempty j := by
    rcases bridge.polyMorphism_nonempty j with
      ⟨lift, hlift⟩
    exact
      ⟨lift.associatedD, lift, hlift, rfl⟩
  evaluationLabel :=
    bridge.evaluationLabel
  evaluationLabel_injective :=
    bridge.evaluationLabel_injective
  evaluationLabel_surjective :=
    bridge.evaluationLabel_surjective

/-- Every selected F-arrow gives a selected arrow of the associated D-bridge. -/
theorem associatedD_mem
    (bridge : SourceFThetaBridge models)
    (j : bridge.capsule.index)
    (arrow :
      bridge.capsule.object j ⟶
        bridge.theater.associatedF)
    (harrow : arrow ∈ bridge.polyMorphism j) :
    arrow.associatedD ∈
      bridge.associatedD.polyMorphism j :=
  ⟨arrow, harrow, rfl⟩

/--
The selected F-arrow over a selected D-arrow is unique.  This is the
Definition 5.5(ii)(d) lifting uniqueness inherited from Corollary 5.3(ii).
-/
theorem associatedD_lift_unique
    (bridge : SourceFThetaBridge models)
    (j : bridge.capsule.index)
    (arrow :
      bridge.associatedD.capsule.object j ⟶
        bridge.associatedD.target)
    (first second :
      bridge.capsule.object j ⟶
        bridge.theater.associatedF)
    (hfirst : first ∈ bridge.polyMorphism j)
    (hsecond : second ∈ bridge.polyMorphism j)
    (hfirst_arrow : first.associatedD = arrow)
    (hsecond_arrow : second.associatedD = arrow) :
    first = second :=
  bridge.associatedD_injective j first second
    hfirst hsecond (hfirst_arrow.trans hsecond_arrow.symm)

/-- The holomorphic procession of the associated D-theta bridge. -/
noncomputable def procession
    (bridge : SourceFThetaBridge models) :
    CategoryProcession
      (CategoryTheory.Cat.of (SourceDPrimeStrip models))
      theta.l.lStarPositive :=
  bridge.associatedD.procession

/-- Exact capsule cardinality in the associated procession. -/
theorem procession_capsule_card
    (bridge : SourceFThetaBridge models)
    (position : Fin theta.l.lStarPositive.1) :
    Fintype.card
      (bridge.procession.capsule position).index =
        position.1 + 1 :=
  bridge.associatedD.procession_capsule_card position

end SourceFThetaBridge

end Iut
