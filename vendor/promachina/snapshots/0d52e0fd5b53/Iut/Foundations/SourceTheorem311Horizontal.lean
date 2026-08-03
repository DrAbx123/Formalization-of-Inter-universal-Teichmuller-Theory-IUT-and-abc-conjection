/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceTheorem311
import Iut.Foundations.SourceTimesMuPrimeStripFullPolyIsomorphism
import Iut.Foundations.SourceTimesMuReconstructionAlgorithm

/-!
# Indexed horizontal compatibility for IUT III, Theorem 3.11(iii)

The four clauses of Theorem 3.11(iii) compare adjacent horizontal columns at
every relevant vertical site, bad place, and absolute label.  This module
records those indices and fixes every corner of the resulting squares to an
actual lattice, prime-strip, projective-system, or labeled-data object.

Clauses (a)--(b) use the Definition 4.9(vii)
`F^(turnstile times-mu)`-prime-strips attached to the actual site and
vertically coric theaters.  Their horizontal arrows are reconstructed from
mono-analytic theta-link members, while the exact fullness assertion of IUT
II, Corollary 4.10(iv), is retained separately from ordinary functoriality.
The older ordinary-`F` square is retained only as preparatory scaffolding.
The indexed corners prevent one unrelated arrow-category square from standing
in for all of clauses (a)--(d).
-/

open CategoryTheory

namespace Iut

universe u v

local infixr:81 " ≫ₚ " =>
  SourceFPrimeStripFullPolyIsomorphism.comp

local infixr:81 " ≫ₜ " =>
  SourceFTimesMuPrimeStripFullPolyIsomorphism.comp

/--
A commutative square with fixed corners and isomorphisms on its two vertical
sides.  Its rows are the horizontal arrows that are compared by Kummer.
-/
structure SourceIndexedHorizontalKummerSquare
    (C : Type u) [Category.{v} C]
    (upperLeft upperRight lowerLeft lowerRight : C) where
  upperHorizontal : upperLeft ⟶ upperRight
  lowerHorizontal : lowerLeft ⟶ lowerRight
  leftKummer : upperLeft ≅ lowerLeft
  rightKummer : upperRight ≅ lowerRight
  commutes :
    leftKummer.hom ≫ lowerHorizontal =
      upperHorizontal ≫ rightKummer.hom

namespace SourceIndexedHorizontalKummerSquare

variable
    {C : Type u} [Category.{v} C]
    {upperLeft upperRight lowerLeft lowerRight : C}

/-- The fixed-corner square as an isomorphism in the arrow category. -/
def toArrowCompatibility
    (square :
      SourceIndexedHorizontalKummerSquare C
        upperLeft upperRight lowerLeft lowerRight) :
    SourceHorizontalKummerCompatibility C where
  sourceHorizontal := Arrow.mk square.upperHorizontal
  targetHorizontal := Arrow.mk square.lowerHorizontal
  verticalKummer :=
    Arrow.isoMk square.leftKummer square.rightKummer square.commutes

/-- Arbitrary automorphisms of the upper row transport to the lower row. -/
def automorphismEquiv
    (square :
      SourceIndexedHorizontalKummerSquare C
        upperLeft upperRight lowerLeft lowerRight) :
    Aut square.toArrowCompatibility.sourceHorizontal ≃*
      Aut square.toArrowCompatibility.targetHorizontal :=
  square.toArrowCompatibility.automorphismEquiv

end SourceIndexedHorizontalKummerSquare

/--
A commutative square in the Section 0 coarsification of `F`-prime-strips.
Every side is an equivalence class of componentwise equivalence maps, not a
strict categorical `Iso` of the prime-strip records.  The chosen horizontal
classes witness nonemptiness; `upperToLower` and `lowerToUpper` express
compatibility of the entire full poly-isomorphisms, not just those witnesses.
-/
structure SourceFPrimeStripPolyIsomorphismSquare
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
    (upperLeft upperRight lowerLeft lowerRight :
      SourceFPrimeStrip models) where
  upperHorizontal :
    SourceFPrimeStripFullPolyIsomorphism upperLeft upperRight
  lowerHorizontal :
    SourceFPrimeStripFullPolyIsomorphism lowerLeft lowerRight
  leftKummer :
    SourceFPrimeStripFullPolyIsomorphism upperLeft lowerLeft
  rightKummer :
    SourceFPrimeStripFullPolyIsomorphism upperRight lowerRight
  commutes :
    SourceFPrimeStripFullPolyIsomorphism.comp
        leftKummer lowerHorizontal =
      SourceFPrimeStripFullPolyIsomorphism.comp
        upperHorizontal rightKummer
  upperToLower :
    ∀ upper : SourceFPrimeStripFullPolyIsomorphism upperLeft upperRight,
      ∃ lower : SourceFPrimeStripFullPolyIsomorphism lowerLeft lowerRight,
        SourceFPrimeStripFullPolyIsomorphism.comp leftKummer lower =
          SourceFPrimeStripFullPolyIsomorphism.comp upper rightKummer
  lowerToUpper :
    ∀ lower : SourceFPrimeStripFullPolyIsomorphism lowerLeft lowerRight,
      ∃ upper : SourceFPrimeStripFullPolyIsomorphism upperLeft upperRight,
        SourceFPrimeStripFullPolyIsomorphism.comp leftKummer lower =
          SourceFPrimeStripFullPolyIsomorphism.comp upper rightKummer

/--
The ordinary-`F` precursor of clause (iii)(a) at `(n,m)`: the upper row
consists of the two site theaters and the lower row of the two vertically
coric theaters.  Its arrows obey the paper's Section 0 coarsification, but the
corners must still be replaced by their Definition 4.9
`F^(turnstile times-mu)` constructions before this is clause (iii)(a) itself.
-/
abbrev SourceTheorem311TrianglePrimeStripSquare
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
    (lattice : SourceAbsoluteLGPGaussianLogThetaLattice models)
    (n m : ℤ) :=
  SourceFPrimeStripPolyIsomorphismSquare
    (lattice.theater n m).associatedF
    (lattice.theater (n + 1) m).associatedF
    (lattice.commonBridge n).theater.associatedF
    (lattice.commonBridge (n + 1)).theater.associatedF

/--
The environment prime strips of clause (iii)(b), together with their natural
comparison isomorphisms to the triangle prime strips at every lattice site.
-/
structure SourceTheorem311EnvironmentPrimeStripFamily
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
    (lattice : SourceAbsoluteLGPGaussianLogThetaLattice models) where
  site : ℤ → ℤ → SourceFPrimeStrip models
  common : ℤ → SourceFPrimeStrip models
  siteToTriangle :
    ∀ n m, SourceFPrimeStripFullPolyIsomorphism
      (site n m) (lattice.theater n m).associatedF
  siteFromTriangle :
    ∀ n m, SourceFPrimeStripFullPolyIsomorphism
      (lattice.theater n m).associatedF (site n m)
  siteToFrom :
    ∀ n m,
      SourceFPrimeStripFullPolyIsomorphism.comp
          (siteToTriangle n m) (siteFromTriangle n m) =
        SourceFPrimeStripFullPolyIsomorphism.id (site n m)
  siteFromTo :
    ∀ n m,
      SourceFPrimeStripFullPolyIsomorphism.comp
          (siteFromTriangle n m) (siteToTriangle n m) =
        SourceFPrimeStripFullPolyIsomorphism.id
          (lattice.theater n m).associatedF
  commonToTriangle :
    ∀ n, SourceFPrimeStripFullPolyIsomorphism
      (common n) (lattice.commonBridge n).theater.associatedF
  commonFromTriangle :
    ∀ n, SourceFPrimeStripFullPolyIsomorphism
      (lattice.commonBridge n).theater.associatedF (common n)
  commonToFrom :
    ∀ n,
      SourceFPrimeStripFullPolyIsomorphism.comp
          (commonToTriangle n) (commonFromTriangle n) =
        SourceFPrimeStripFullPolyIsomorphism.id (common n)
  commonFromTo :
    ∀ n,
      SourceFPrimeStripFullPolyIsomorphism.comp
          (commonFromTriangle n) (commonToTriangle n) =
        SourceFPrimeStripFullPolyIsomorphism.id
          (lattice.commonBridge n).theater.associatedF

/-- The ordinary-`F` precursor of the fixed-corner square in clause (iii)(b). -/
abbrev SourceTheorem311EnvironmentPrimeStripSquare
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
    {lattice : SourceAbsoluteLGPGaussianLogThetaLattice models}
    (family : SourceTheorem311EnvironmentPrimeStripFamily lattice)
    (n m : ℤ) :=
  SourceFPrimeStripPolyIsomorphismSquare
    (family.site n m) (family.site (n + 1) m)
    (family.common n) (family.common (n + 1))

namespace SourceTheorem311EnvironmentPrimeStripSquare

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
    {lattice : SourceAbsoluteLGPGaussianLogThetaLattice models}

/--
Clause (iii)(b) is obtained from clause (iii)(a) by conjugating all four
sides with the natural environment-to-triangle comparison isomorphisms.
-/
def ofTriangle
    (family : SourceTheorem311EnvironmentPrimeStripFamily lattice)
    (n m : ℤ)
    (triangle : SourceTheorem311TrianglePrimeStripSquare lattice n m) :
    SourceTheorem311EnvironmentPrimeStripSquare family n m where
  upperHorizontal :=
    SourceFPrimeStripFullPolyIsomorphism.comp
      (SourceFPrimeStripFullPolyIsomorphism.comp
        (family.siteToTriangle n m) triangle.upperHorizontal)
      (family.siteFromTriangle (n + 1) m)
  lowerHorizontal :=
    SourceFPrimeStripFullPolyIsomorphism.comp
      (SourceFPrimeStripFullPolyIsomorphism.comp
        (family.commonToTriangle n) triangle.lowerHorizontal)
      (family.commonFromTriangle (n + 1))
  leftKummer :=
    SourceFPrimeStripFullPolyIsomorphism.comp
      (SourceFPrimeStripFullPolyIsomorphism.comp
        (family.siteToTriangle n m) triangle.leftKummer)
      (family.commonFromTriangle n)
  rightKummer :=
    SourceFPrimeStripFullPolyIsomorphism.comp
      (SourceFPrimeStripFullPolyIsomorphism.comp
        (family.siteToTriangle (n + 1) m) triangle.rightKummer)
      (family.commonFromTriangle (n + 1))
  commutes := by
    have commonCancellation :
        family.commonFromTriangle n ≫ₚ
            (family.commonToTriangle n ≫ₚ
              (triangle.lowerHorizontal ≫ₚ
                family.commonFromTriangle (n + 1))) =
          triangle.lowerHorizontal ≫ₚ
            family.commonFromTriangle (n + 1) :=
      SourceFPrimeStripFullPolyIsomorphism.comp_inverse_assoc
        (family.commonFromTriangle n)
        (family.commonToTriangle n)
        (family.commonFromTo n)
        (triangle.lowerHorizontal ≫ₚ
          family.commonFromTriangle (n + 1))
    have siteCancellation :
        family.siteFromTriangle (n + 1) m ≫ₚ
            (family.siteToTriangle (n + 1) m ≫ₚ
              (triangle.rightKummer ≫ₚ
                family.commonFromTriangle (n + 1))) =
          triangle.rightKummer ≫ₚ
            family.commonFromTriangle (n + 1) :=
      SourceFPrimeStripFullPolyIsomorphism.comp_inverse_assoc
        (family.siteFromTriangle (n + 1) m)
        (family.siteToTriangle (n + 1) m)
        (family.siteFromTo (n + 1) m)
        (triangle.rightKummer ≫ₚ
          family.commonFromTriangle (n + 1))
    calc
      ((family.siteToTriangle n m ≫ₚ triangle.leftKummer) ≫ₚ
          family.commonFromTriangle n) ≫ₚ
          ((family.commonToTriangle n ≫ₚ
            triangle.lowerHorizontal) ≫ₚ
            family.commonFromTriangle (n + 1)) =
        family.siteToTriangle n m ≫ₚ
          (triangle.leftKummer ≫ₚ
            (family.commonFromTriangle n ≫ₚ
              (family.commonToTriangle n ≫ₚ
                (triangle.lowerHorizontal ≫ₚ
                  family.commonFromTriangle (n + 1))))) := by
            simp only [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
      _ = family.siteToTriangle n m ≫ₚ
          (triangle.leftKummer ≫ₚ
            (triangle.lowerHorizontal ≫ₚ
              family.commonFromTriangle (n + 1))) := by
            rw [commonCancellation]
      _ = family.siteToTriangle n m ≫ₚ
          ((triangle.leftKummer ≫ₚ triangle.lowerHorizontal) ≫ₚ
            family.commonFromTriangle (n + 1)) := by
            rw [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
      _ = family.siteToTriangle n m ≫ₚ
          ((triangle.upperHorizontal ≫ₚ triangle.rightKummer) ≫ₚ
            family.commonFromTriangle (n + 1)) := by
            rw [triangle.commutes]
      _ = family.siteToTriangle n m ≫ₚ
          (triangle.upperHorizontal ≫ₚ
            (triangle.rightKummer ≫ₚ
              family.commonFromTriangle (n + 1))) := by
            rw [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
      _ = family.siteToTriangle n m ≫ₚ
          (triangle.upperHorizontal ≫ₚ
            (family.siteFromTriangle (n + 1) m ≫ₚ
              (family.siteToTriangle (n + 1) m ≫ₚ
                (triangle.rightKummer ≫ₚ
                  family.commonFromTriangle (n + 1))))) := by
            rw [siteCancellation]
      _ = ((family.siteToTriangle n m ≫ₚ
          triangle.upperHorizontal) ≫ₚ
          family.siteFromTriangle (n + 1) m) ≫ₚ
          ((family.siteToTriangle (n + 1) m ≫ₚ
            triangle.rightKummer) ≫ₚ
            family.commonFromTriangle (n + 1)) := by
            simp only [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
  upperToLower := by
    intro upper
    let triangleUpper :=
      (family.siteFromTriangle n m ≫ₚ upper) ≫ₚ
        family.siteToTriangle (n + 1) m
    rcases triangle.upperToLower triangleUpper with
      ⟨triangleLower, triangleCommutes⟩
    refine
      ⟨(family.commonToTriangle n ≫ₚ triangleLower) ≫ₚ
          family.commonFromTriangle (n + 1), ?_⟩
    simp only [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
    rw [SourceFPrimeStripFullPolyIsomorphism.comp_inverse_assoc
      (family.commonFromTriangle n)
      (family.commonToTriangle n)
      (family.commonFromTo n)]
    rw [← SourceFPrimeStripFullPolyIsomorphism.comp_assoc
      triangle.leftKummer triangleLower
      (family.commonFromTriangle (n + 1))]
    rw [triangleCommutes]
    dsimp [triangleUpper]
    simp only [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
    rw [SourceFPrimeStripFullPolyIsomorphism.comp_inverse_assoc
      (family.siteToTriangle n m)
      (family.siteFromTriangle n m)
      (family.siteToFrom n m)]
  lowerToUpper := by
    intro lower
    let triangleLower :=
      (family.commonFromTriangle n ≫ₚ lower) ≫ₚ
        family.commonToTriangle (n + 1)
    rcases triangle.lowerToUpper triangleLower with
      ⟨triangleUpper, triangleCommutes⟩
    refine
      ⟨(family.siteToTriangle n m ≫ₚ triangleUpper) ≫ₚ
          family.siteFromTriangle (n + 1) m, ?_⟩
    simp only [SourceFPrimeStripFullPolyIsomorphism.comp_assoc]
    rw [SourceFPrimeStripFullPolyIsomorphism.comp_inverse_assoc
      (family.siteFromTriangle (n + 1) m)
      (family.siteToTriangle (n + 1) m)
      (family.siteFromTo (n + 1) m)]
    have extended := congrArg
      (fun map => map ≫ₚ family.commonFromTriangle (n + 1))
      triangleCommutes
    dsimp [triangleLower] at extended
    simp only [SourceFPrimeStripFullPolyIsomorphism.comp_assoc] at extended
    rw [family.commonToFrom (n + 1)] at extended
    simp only [SourceFPrimeStripFullPolyIsomorphism.comp_id] at extended
    rw [extended]

end SourceTheorem311EnvironmentPrimeStripSquare

/-! ## Exact times-mu squares of clauses (iii)(a)-(b) -/

/--
A commutative square in the Section 0 coarsification of the place-indexed
`F^(turnstile times-mu)`-prime-strips of IUT II, Definition 4.9(vii).

The four underlying mono-analytic strips may differ.  This is essential for
Theorem 3.11(iii): its upper row belongs to two adjacent theta-Hodge theaters,
whereas its lower row belongs to their vertically coric theaters.
-/
structure SourceFTimesMuPrimeStripPolyIsomorphismSquare
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
    {upperLeftUnderlying upperRightUnderlying
      lowerLeftUnderlying lowerRightUnderlying :
        SourceFMonoAnalyticPrimeStrip models}
    (upperLeft : SourceFTimesMuPrimeStrip upperLeftUnderlying)
    (upperRight : SourceFTimesMuPrimeStrip upperRightUnderlying)
    (lowerLeft : SourceFTimesMuPrimeStrip lowerLeftUnderlying)
    (lowerRight : SourceFTimesMuPrimeStrip lowerRightUnderlying) where
  upperHorizontal :
    SourceFTimesMuPrimeStripFullPolyIsomorphism upperLeft upperRight
  lowerHorizontal :
    SourceFTimesMuPrimeStripFullPolyIsomorphism lowerLeft lowerRight
  leftKummer :
    SourceFTimesMuPrimeStripFullPolyIsomorphism upperLeft lowerLeft
  rightKummer :
    SourceFTimesMuPrimeStripFullPolyIsomorphism upperRight lowerRight
  commutes :
    leftKummer ≫ₜ lowerHorizontal = upperHorizontal ≫ₜ rightKummer
  upperToLower :
    ∀ upper : SourceFTimesMuPrimeStripFullPolyIsomorphism
        upperLeft upperRight,
      ∃ lower : SourceFTimesMuPrimeStripFullPolyIsomorphism
          lowerLeft lowerRight,
        leftKummer ≫ₜ lower = upper ≫ₜ rightKummer
  lowerToUpper :
    ∀ lower : SourceFTimesMuPrimeStripFullPolyIsomorphism
        lowerLeft lowerRight,
      ∃ upper : SourceFTimesMuPrimeStripFullPolyIsomorphism
          upperLeft upperRight,
        leftKummer ≫ₜ lower = upper ≫ₜ rightKummer

namespace SourceFTimesMuPrimeStripPolyIsomorphismSquare

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
    {upperLeftUnderlying upperRightUnderlying
      lowerLeftUnderlying lowerRightUnderlying :
        SourceFMonoAnalyticPrimeStrip models}
    {upperLeft : SourceFTimesMuPrimeStrip upperLeftUnderlying}
    {upperRight : SourceFTimesMuPrimeStrip upperRightUnderlying}
    {lowerLeft : SourceFTimesMuPrimeStrip lowerLeftUnderlying}
    {lowerRight : SourceFTimesMuPrimeStrip lowerRightUnderlying}

/--
Construct the full compatibility square from one upper-row member and
two-sided Kummer comparisons.  The lower row and both directions of
full-poly compatibility are forced by conjugation.
-/
noncomputable def ofUpperHorizontal
    (upperHorizontal :
      SourceFTimesMuPrimeStripFullPolyIsomorphism upperLeft upperRight)
    (leftKummer :
      SourceFTimesMuPrimeStripFullPolyIsomorphism upperLeft lowerLeft)
    (leftKummerInverse :
      SourceFTimesMuPrimeStripFullPolyIsomorphism lowerLeft upperLeft)
    (leftToFrom : leftKummer ≫ₜ leftKummerInverse =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.id upperLeft)
    (rightKummer :
      SourceFTimesMuPrimeStripFullPolyIsomorphism upperRight lowerRight)
    (rightKummerInverse :
      SourceFTimesMuPrimeStripFullPolyIsomorphism lowerRight upperRight)
    (rightFromTo : rightKummerInverse ≫ₜ rightKummer =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.id lowerRight) :
    SourceFTimesMuPrimeStripPolyIsomorphismSquare
      upperLeft upperRight lowerLeft lowerRight where
  upperHorizontal := upperHorizontal
  lowerHorizontal := (leftKummerInverse ≫ₜ upperHorizontal) ≫ₜ rightKummer
  leftKummer := leftKummer
  rightKummer := rightKummer
  commutes := by
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
      leftKummerInverse upperHorizontal rightKummer]
    exact SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_inverse_assoc
      leftKummer leftKummerInverse leftToFrom
      (upperHorizontal ≫ₜ rightKummer)
  upperToLower upper := by
    refine ⟨(leftKummerInverse ≫ₜ upper) ≫ₜ rightKummer, ?_⟩
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
      leftKummerInverse upper rightKummer]
    exact SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_inverse_assoc
      leftKummer leftKummerInverse leftToFrom (upper ≫ₜ rightKummer)
  lowerToUpper lower := by
    refine ⟨(leftKummer ≫ₜ lower) ≫ₜ rightKummerInverse, ?_⟩
    symm
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
      (leftKummer ≫ₜ lower) rightKummerInverse rightKummer]
    rw [rightFromTo]
    exact SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_id _

end SourceFTimesMuPrimeStripPolyIsomorphismSquare

/--
The Definition 4.9(vii) prime-strips at all site and vertically coric
endpoints of the LGP lattice.

Every strip is definitionally based on the mono-analytic `F`-prime-strip
constructed from its own theater by the Corollaries 4.5/4.6 transport.  Thus
the family cannot be populated by unrelated times-mu records.  Constructing
these transports and strips is the Corollary 4.10 source obligation.
-/
structure SourceTheorem311TimesMuPrimeStripFamily
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
    (lattice : SourceAbsoluteLGPGaussianLogThetaLattice models) where
  siteTransport :
    ∀ n m, (lattice.theater n m).MonoAnalyticTransport
  site :
    ∀ n m,
      SourceFTimesMuPrimeStrip
        ((lattice.theater n m).associatedFMonoAnalytic
          (siteTransport n m))
  commonTransport :
    ∀ n, (lattice.commonBridge n).theater.MonoAnalyticTransport
  common :
    ∀ n,
      SourceFTimesMuPrimeStrip
        ((lattice.commonBridge n).theater.associatedFMonoAnalytic
          (commonTransport n))

/--
The Corollary 4.10 construction data for every site and vertically coric
theater of one LGP lattice.  The times-mu strips themselves are computed by
`toFamily`; they are not fields of this record.
-/
structure SourceTheorem311TimesMuPrimeStripConstruction
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
    (lattice : SourceAbsoluteLGPGaussianLogThetaLattice models) where
  reconstruction : SourceFTimesMuReconstructionAlgorithm models
  siteTransport :
    ∀ n m, (lattice.theater n m).MonoAnalyticTransport
  commonTransport :
    ∀ n, (lattice.commonBridge n).theater.MonoAnalyticTransport
  horizontalFullness :
    ∀ n m,
      SourceFTimesMuReconstructionFullness
        reconstruction.objects reconstruction.transport
        ((lattice.theater n m).associatedFMonoAnalytic
          (siteTransport n m))
        ((lattice.theater (n + 1) m).associatedFMonoAnalytic
          (siteTransport (n + 1) m))

namespace SourceTheorem311TimesMuPrimeStripConstruction

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
    {lattice : SourceAbsoluteLGPGaussianLogThetaLattice models}

/-- The mono-analytic source strip at one lattice site. -/
def siteUnderlying
    (construction : SourceTheorem311TimesMuPrimeStripConstruction lattice)
    (n m : ℤ) : SourceFMonoAnalyticPrimeStrip models :=
  (lattice.theater n m).associatedFMonoAnalytic
    (construction.siteTransport n m)

/-- The mono-analytic source strip at one vertically coric endpoint. -/
def commonUnderlying
    (construction : SourceTheorem311TimesMuPrimeStripConstruction lattice)
    (n : ℤ) : SourceFMonoAnalyticPrimeStrip models :=
  (lattice.commonBridge n).theater.associatedFMonoAnalytic
    (construction.commonTransport n)

/-- Compute all theorem endpoints by the one functorial reconstruction algorithm. -/
def toFamily
    (construction : SourceTheorem311TimesMuPrimeStripConstruction lattice) :
    SourceTheorem311TimesMuPrimeStripFamily lattice where
  siteTransport := construction.siteTransport
  site n m :=
    construction.reconstruction.obj (construction.siteUnderlying n m)
  commonTransport := construction.commonTransport
  common n :=
    construction.reconstruction.obj (construction.commonUnderlying n)

end SourceTheorem311TimesMuPrimeStripConstruction

/-!
## Corollary 4.10(iv) and Theorem 1.5 horizontal coricity
-/

/-
The Corollary 4.10(iv) and Theorem 1.5 data that produce the horizontal
`F^(turnstile times-mu)` square are consequences of the exact reconstruction
and mono-analytic model-comparison records.

The literal Section 0 content of IUT II, Corollary 4.10(iv), is carried by the
reconstruction algorithm's representative-level fullness law: every output
isomorphism class has a mono-analytic theta-link preimage.

The theta-link and Kummer members are both obtained by composing the certified
two-sided comparisons through the common Examples 3.2--3.4 model.  Their
inverse laws follow from the model-comparison coherence stored by the exact
mono-analytic prime strips.  No chosen horizontal or Kummer maps remain.
-/
namespace SourceTheorem311TimesMuPrimeStripConstruction

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
    {lattice : SourceAbsoluteLGPGaussianLogThetaLattice models}
    (construction : SourceTheorem311TimesMuPrimeStripConstruction lattice)

/--
The exact Corollary 4.10(iv) fullness assertion, derived from the
representative-level reconstruction law rather than stored on the corridor.
-/
theorem thetaLink_full
    (n m : ℤ)
    (horizontal : SourceFTimesMuPrimeStripFullPolyIsomorphism
      (construction.toFamily.site n m)
      (construction.toFamily.site (n + 1) m)) :
    ∃ link : SourceFMonoAnalyticPrimeStripFullPolyIsomorphism
        (construction.siteUnderlying n m)
        (construction.siteUnderlying (n + 1) m),
      construction.reconstruction.mapFullPolyIsomorphism link = horizontal :=
  construction.reconstruction.mapFullPolyIsomorphism_surjective
    (construction.horizontalFullness n m) horizontal

/-- The horizontal times-mu member induced by the mono-analytic theta link. -/
def horizontal
    (n m : ℤ) : SourceFTimesMuPrimeStripFullPolyIsomorphism
      (construction.toFamily.site n m)
      (construction.toFamily.site (n + 1) m) :=
  construction.reconstruction.mapFullPolyIsomorphism
    (SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.canonical
      (construction.siteUnderlying n m)
      (construction.siteUnderlying (n + 1) m))

/-- The Kummer comparison induced by reconstruction. -/
def toCommon
    (n m : ℤ) : SourceFTimesMuPrimeStripFullPolyIsomorphism
      (construction.toFamily.site n m)
      (construction.toFamily.common n) :=
  construction.reconstruction.mapFullPolyIsomorphism
    (SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.canonical
      (construction.siteUnderlying n m)
      (construction.commonUnderlying n))

/-- The inverse Kummer comparison induced by reconstruction. -/
def fromCommon
    (n m : ℤ) : SourceFTimesMuPrimeStripFullPolyIsomorphism
      (construction.toFamily.common n)
      (construction.toFamily.site n m) :=
  construction.reconstruction.mapFullPolyIsomorphism
    (SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.canonical
      (construction.commonUnderlying n)
      (construction.siteUnderlying n m))

/-- The reconstructed Kummer comparison followed by its inverse is identity. -/
theorem toFrom
    (n m : ℤ) :
    (construction.toCommon n m) ≫ₜ (construction.fromCommon n m) =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.id
        (construction.toFamily.site n m) :=
  construction.reconstruction.mapFullPolyIsomorphism_inverse
    (SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.canonical
      (construction.siteUnderlying n m)
      (construction.commonUnderlying n))
    (SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.canonical
      (construction.commonUnderlying n)
      (construction.siteUnderlying n m))
    (SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.canonical_inverse
      (construction.siteUnderlying n m)
      (construction.commonUnderlying n))

/-- The inverse reconstructed Kummer comparison followed by it is identity. -/
theorem fromTo
    (n m : ℤ) :
    (construction.fromCommon n m) ≫ₜ (construction.toCommon n m) =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.id
        (construction.toFamily.common n) :=
  construction.reconstruction.mapFullPolyIsomorphism_inverse
    (SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.canonical
      (construction.commonUnderlying n)
      (construction.siteUnderlying n m))
    (SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.canonical
      (construction.siteUnderlying n m)
      (construction.commonUnderlying n))
    (SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.canonical_inverse
      (construction.commonUnderlying n)
      (construction.siteUnderlying n m))

/--
The exact Theorem 3.11(iii)(a) square, with its lower horizontal arrow and
full-poly compatibility derived by Kummer conjugation.
-/
noncomputable def toTriangleSquare
    (n m : ℤ) :
    SourceFTimesMuPrimeStripPolyIsomorphismSquare
      (construction.toFamily.site n m)
      (construction.toFamily.site (n + 1) m)
      (construction.toFamily.common n)
      (construction.toFamily.common (n + 1)) :=
  SourceFTimesMuPrimeStripPolyIsomorphismSquare.ofUpperHorizontal
    (construction.horizontal n m)
    (construction.toCommon n m)
    (construction.fromCommon n m)
    (construction.toFrom n m)
    (construction.toCommon (n + 1) m)
    (construction.fromCommon (n + 1) m)
    (construction.fromTo (n + 1) m)

end SourceTheorem311TimesMuPrimeStripConstruction

/--
The Proposition 2.1(vi) environment objects and natural comparisons before
times-mu reconstruction.  The comparison maps are full Section 0 classes of
mono-analytic prime-strip equivalences, with selected two-sided inverses.
-/
structure SourceTheorem311EnvironmentMonoAnalyticPrimeStripFamily
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
    {lattice : SourceAbsoluteLGPGaussianLogThetaLattice models}
    (construction : SourceTheorem311TimesMuPrimeStripConstruction lattice) where
  site : ℤ → ℤ → SourceFMonoAnalyticPrimeStrip models
  common : ℤ → SourceFMonoAnalyticPrimeStrip models
  siteToTriangle :
    ∀ n m, SourceFMonoAnalyticPrimeStripFullPolyIsomorphism
      (site n m) (construction.siteUnderlying n m)
  siteFromTriangle :
    ∀ n m, SourceFMonoAnalyticPrimeStripFullPolyIsomorphism
      (construction.siteUnderlying n m) (site n m)
  siteToFrom :
    ∀ n m,
      SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.comp
          (siteToTriangle n m) (siteFromTriangle n m) =
        SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.id (site n m)
  siteFromTo :
    ∀ n m,
      SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.comp
          (siteFromTriangle n m) (siteToTriangle n m) =
        SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.id
          (construction.siteUnderlying n m)
  commonToTriangle :
    ∀ n, SourceFMonoAnalyticPrimeStripFullPolyIsomorphism
      (common n) (construction.commonUnderlying n)
  commonFromTriangle :
    ∀ n, SourceFMonoAnalyticPrimeStripFullPolyIsomorphism
      (construction.commonUnderlying n) (common n)
  commonToFrom :
    ∀ n,
      SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.comp
          (commonToTriangle n) (commonFromTriangle n) =
        SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.id (common n)
  commonFromTo :
    ∀ n,
      SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.comp
          (commonFromTriangle n) (commonToTriangle n) =
        SourceFMonoAnalyticPrimeStripFullPolyIsomorphism.id
          (construction.commonUnderlying n)

/-- The exact fixed-corner square asserted in Theorem 3.11(iii)(a). -/
abbrev SourceTheorem311TimesMuTrianglePrimeStripSquare
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
    {lattice : SourceAbsoluteLGPGaussianLogThetaLattice models}
    (family : SourceTheorem311TimesMuPrimeStripFamily lattice)
    (n m : ℤ) :=
  SourceFTimesMuPrimeStripPolyIsomorphismSquare
    (family.site n m) (family.site (n + 1) m)
    (family.common n) (family.common (n + 1))

/--
The environment `F^(turnstile times-mu)`-prime-strips of clause (iii)(b).
The comparison maps are the natural isomorphisms of Proposition 2.1(vi), and
both composites are required to be identities in the Section 0 quotient.
-/
structure SourceTheorem311EnvironmentTimesMuPrimeStripFamily
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
    {lattice : SourceAbsoluteLGPGaussianLogThetaLattice models}
    (triangle : SourceTheorem311TimesMuPrimeStripFamily lattice) where
  siteUnderlying : ℤ → ℤ → SourceFMonoAnalyticPrimeStrip models
  site :
    ∀ n m, SourceFTimesMuPrimeStrip (siteUnderlying n m)
  commonUnderlying : ℤ → SourceFMonoAnalyticPrimeStrip models
  common :
    ∀ n, SourceFTimesMuPrimeStrip (commonUnderlying n)
  siteToTriangle :
    ∀ n m, SourceFTimesMuPrimeStripFullPolyIsomorphism
      (site n m) (triangle.site n m)
  siteFromTriangle :
    ∀ n m, SourceFTimesMuPrimeStripFullPolyIsomorphism
      (triangle.site n m) (site n m)
  siteToFrom :
    ∀ n m, (siteToTriangle n m) ≫ₜ (siteFromTriangle n m) =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.id (site n m)
  siteFromTo :
    ∀ n m, (siteFromTriangle n m) ≫ₜ (siteToTriangle n m) =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.id (triangle.site n m)
  commonToTriangle :
    ∀ n, SourceFTimesMuPrimeStripFullPolyIsomorphism
      (common n) (triangle.common n)
  commonFromTriangle :
    ∀ n, SourceFTimesMuPrimeStripFullPolyIsomorphism
      (triangle.common n) (common n)
  commonToFrom :
    ∀ n, (commonToTriangle n) ≫ₜ (commonFromTriangle n) =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.id (common n)
  commonFromTo :
    ∀ n, (commonFromTriangle n) ≫ₜ (commonToTriangle n) =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.id (triangle.common n)

namespace SourceTheorem311EnvironmentMonoAnalyticPrimeStripFamily

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
    {lattice : SourceAbsoluteLGPGaussianLogThetaLattice models}
    {construction : SourceTheorem311TimesMuPrimeStripConstruction lattice}

/--
Apply the Definition 4.9(vi) functor to every environment object and every
Proposition 2.1(vi) comparison.  All inverse laws are derived from functoriality.
-/
def toTimesMu
    (family :
      SourceTheorem311EnvironmentMonoAnalyticPrimeStripFamily construction) :
    SourceTheorem311EnvironmentTimesMuPrimeStripFamily
      construction.toFamily where
  siteUnderlying := family.site
  site n m := construction.reconstruction.obj (family.site n m)
  commonUnderlying := family.common
  common n := construction.reconstruction.obj (family.common n)
  siteToTriangle n m :=
    construction.reconstruction.mapFullPolyIsomorphism
      (family.siteToTriangle n m)
  siteFromTriangle n m :=
    construction.reconstruction.mapFullPolyIsomorphism
      (family.siteFromTriangle n m)
  siteToFrom n m :=
    construction.reconstruction.mapFullPolyIsomorphism_inverse
      (family.siteToTriangle n m) (family.siteFromTriangle n m)
      (family.siteToFrom n m)
  siteFromTo n m :=
    construction.reconstruction.mapFullPolyIsomorphism_inverse
      (family.siteFromTriangle n m) (family.siteToTriangle n m)
      (family.siteFromTo n m)
  commonToTriangle n :=
    construction.reconstruction.mapFullPolyIsomorphism
      (family.commonToTriangle n)
  commonFromTriangle n :=
    construction.reconstruction.mapFullPolyIsomorphism
      (family.commonFromTriangle n)
  commonToFrom n :=
    construction.reconstruction.mapFullPolyIsomorphism_inverse
      (family.commonToTriangle n) (family.commonFromTriangle n)
      (family.commonToFrom n)
  commonFromTo n :=
    construction.reconstruction.mapFullPolyIsomorphism_inverse
      (family.commonFromTriangle n) (family.commonToTriangle n)
      (family.commonFromTo n)

end SourceTheorem311EnvironmentMonoAnalyticPrimeStripFamily

/-- The exact fixed-corner square asserted in Theorem 3.11(iii)(b). -/
abbrev SourceTheorem311EnvironmentTimesMuPrimeStripSquare
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
    {lattice : SourceAbsoluteLGPGaussianLogThetaLattice models}
    {triangle : SourceTheorem311TimesMuPrimeStripFamily lattice}
    (family : SourceTheorem311EnvironmentTimesMuPrimeStripFamily triangle)
    (n m : ℤ) :=
  SourceFTimesMuPrimeStripPolyIsomorphismSquare
    (family.site n m) (family.site (n + 1) m)
    (family.common n) (family.common (n + 1))

namespace SourceTheorem311EnvironmentTimesMuPrimeStripSquare

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
    {lattice : SourceAbsoluteLGPGaussianLogThetaLattice models}
    {triangle : SourceTheorem311TimesMuPrimeStripFamily lattice}

/--
Clause (iii)(b) follows from clause (iii)(a) by conjugating all four sides
with the natural environment-to-triangle isomorphisms.
-/
noncomputable def ofTriangle
    (family : SourceTheorem311EnvironmentTimesMuPrimeStripFamily triangle)
    (n m : ℤ)
    (square : SourceTheorem311TimesMuTrianglePrimeStripSquare triangle n m) :
    SourceTheorem311EnvironmentTimesMuPrimeStripSquare family n m where
  upperHorizontal :=
    ((family.siteToTriangle n m) ≫ₜ square.upperHorizontal) ≫ₜ
      (family.siteFromTriangle (n + 1) m)
  lowerHorizontal :=
    ((family.commonToTriangle n) ≫ₜ square.lowerHorizontal) ≫ₜ
      (family.commonFromTriangle (n + 1))
  leftKummer :=
    ((family.siteToTriangle n m) ≫ₜ square.leftKummer) ≫ₜ
      (family.commonFromTriangle n)
  rightKummer :=
    ((family.siteToTriangle (n + 1) m) ≫ₜ square.rightKummer) ≫ₜ
      (family.commonFromTriangle (n + 1))
  commutes := by
    have commonCancellation :
        family.commonFromTriangle n ≫ₜ
            (family.commonToTriangle n ≫ₜ
              (square.lowerHorizontal ≫ₜ
                family.commonFromTriangle (n + 1))) =
          square.lowerHorizontal ≫ₜ
            family.commonFromTriangle (n + 1) :=
      SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_inverse_assoc
        (family.commonFromTriangle n)
        (family.commonToTriangle n)
        (family.commonFromTo n)
        (square.lowerHorizontal ≫ₜ family.commonFromTriangle (n + 1))
    have siteCancellation :
        family.siteFromTriangle (n + 1) m ≫ₜ
            (family.siteToTriangle (n + 1) m ≫ₜ
              (square.rightKummer ≫ₜ
                family.commonFromTriangle (n + 1))) =
          square.rightKummer ≫ₜ family.commonFromTriangle (n + 1) :=
      SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_inverse_assoc
        (family.siteFromTriangle (n + 1) m)
        (family.siteToTriangle (n + 1) m)
        (family.siteFromTo (n + 1) m)
        (square.rightKummer ≫ₜ family.commonFromTriangle (n + 1))
    calc
      (((family.siteToTriangle n m ≫ₜ square.leftKummer) ≫ₜ
          family.commonFromTriangle n) ≫ₜ
          ((family.commonToTriangle n ≫ₜ square.lowerHorizontal) ≫ₜ
            family.commonFromTriangle (n + 1))) =
        family.siteToTriangle n m ≫ₜ
          (square.leftKummer ≫ₜ
            (family.commonFromTriangle n ≫ₜ
              (family.commonToTriangle n ≫ₜ
                (square.lowerHorizontal ≫ₜ
                  family.commonFromTriangle (n + 1))))) := by
            simp only [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc]
      _ = family.siteToTriangle n m ≫ₜ
          (square.leftKummer ≫ₜ
            (square.lowerHorizontal ≫ₜ
              family.commonFromTriangle (n + 1))) := by
            rw [commonCancellation]
      _ = family.siteToTriangle n m ≫ₜ
          ((square.leftKummer ≫ₜ square.lowerHorizontal) ≫ₜ
            family.commonFromTriangle (n + 1)) := by
            rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc]
      _ = family.siteToTriangle n m ≫ₜ
          ((square.upperHorizontal ≫ₜ square.rightKummer) ≫ₜ
            family.commonFromTriangle (n + 1)) := by
            rw [square.commutes]
      _ = family.siteToTriangle n m ≫ₜ
          (square.upperHorizontal ≫ₜ
            (square.rightKummer ≫ₜ
              family.commonFromTriangle (n + 1))) := by
            rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc]
      _ = family.siteToTriangle n m ≫ₜ
          (square.upperHorizontal ≫ₜ
            (family.siteFromTriangle (n + 1) m ≫ₜ
              (family.siteToTriangle (n + 1) m ≫ₜ
                (square.rightKummer ≫ₜ
                  family.commonFromTriangle (n + 1))))) := by
            rw [siteCancellation]
      _ = (((family.siteToTriangle n m ≫ₜ square.upperHorizontal) ≫ₜ
          family.siteFromTriangle (n + 1) m) ≫ₜ
          ((family.siteToTriangle (n + 1) m ≫ₜ square.rightKummer) ≫ₜ
            family.commonFromTriangle (n + 1))) := by
            simp only [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc]
  upperToLower := by
    intro upper
    let triangleUpper :=
      (family.siteFromTriangle n m ≫ₜ upper) ≫ₜ
        family.siteToTriangle (n + 1) m
    rcases square.upperToLower triangleUpper with
      ⟨triangleLower, triangleCommutes⟩
    refine
      ⟨(family.commonToTriangle n ≫ₜ triangleLower) ≫ₜ
          family.commonFromTriangle (n + 1), ?_⟩
    simp only [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc]
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_inverse_assoc
      (family.commonFromTriangle n)
      (family.commonToTriangle n)
      (family.commonFromTo n)]
    rw [← SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
      square.leftKummer triangleLower
      (family.commonFromTriangle (n + 1))]
    rw [triangleCommutes]
    dsimp [triangleUpper]
    simp only [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc]
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_inverse_assoc
      (family.siteToTriangle n m)
      (family.siteFromTriangle n m)
      (family.siteToFrom n m)]
  lowerToUpper := by
    intro lower
    let triangleLower :=
      (family.commonFromTriangle n ≫ₜ lower) ≫ₜ
        family.commonToTriangle (n + 1)
    rcases square.lowerToUpper triangleLower with
      ⟨triangleUpper, triangleCommutes⟩
    refine
      ⟨(family.siteToTriangle n m ≫ₜ triangleUpper) ≫ₜ
          family.siteFromTriangle (n + 1) m, ?_⟩
    simp only [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc]
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_inverse_assoc
      (family.siteFromTriangle (n + 1) m)
      (family.siteToTriangle (n + 1) m)
      (family.siteFromTo (n + 1) m)]
    have extended := congrArg
      (fun map => map ≫ₜ family.commonFromTriangle (n + 1))
      triangleCommutes
    dsimp [triangleLower] at extended
    simp only [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc] at extended
    rw [family.commonToFrom (n + 1)] at extended
    simp only [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_id] at extended
    rw [extended]

end SourceTheorem311EnvironmentTimesMuPrimeStripSquare

/--
A fixed-corner square of actual mono-theta projective systems.  Each side is
an isomorphism carrying its levelwise environment realization.
-/
structure SourceIndexedMonoThetaProjectiveSystemSquare
    (upperLeft upperRight lowerLeft lowerRight :
      SourceMonoThetaProjectiveSystem.{u}) where
  upperHorizontal :
    SourceMonoThetaProjectiveSystemIso upperLeft upperRight
  lowerHorizontal :
    SourceMonoThetaProjectiveSystemIso lowerLeft lowerRight
  leftKummer :
    SourceMonoThetaProjectiveSystemIso upperLeft lowerLeft
  rightKummer :
    SourceMonoThetaProjectiveSystemIso upperRight lowerRight
  commutes :
    leftKummer.groupDiagramIso.hom ≫
        lowerHorizontal.groupDiagramIso.hom =
      upperHorizontal.groupDiagramIso.hom ≫
        rightKummer.groupDiagramIso.hom

namespace SourceIndexedMonoThetaProjectiveSystemSquare

variable
    {upperLeft upperRight lowerLeft lowerRight :
      SourceMonoThetaProjectiveSystem.{u}}

/-- The projective-system square as a fixed-corner arrow isomorphism. -/
def toKummerSquare
    (square :
      SourceIndexedMonoThetaProjectiveSystemSquare
        upperLeft upperRight lowerLeft lowerRight) :
    SourceIndexedHorizontalKummerSquare
      (MonoThetaModulus ⥤ TopologicalGroupCat.{u})
      upperLeft.groupDiagram upperRight.groupDiagram
      lowerLeft.groupDiagram lowerRight.groupDiagram where
  upperHorizontal := square.upperHorizontal.groupDiagramIso.hom
  lowerHorizontal := square.lowerHorizontal.groupDiagramIso.hom
  leftKummer := square.leftKummer.groupDiagramIso
  rightKummer := square.rightKummer.groupDiagramIso
  commutes := square.commutes

end SourceIndexedMonoThetaProjectiveSystemSquare

/--
The site and vertically coric projective systems used in clause (iii)(c),
indexed by both lattice coordinates and the actual selected bad place.
-/
structure SourceTheorem311MonoThetaProjectiveSystemFamily
    (badPlace : Type u) where
  site : ℤ → ℤ → badPlace → SourceMonoThetaProjectiveSystem.{u}
  common : ℤ → badPlace → SourceMonoThetaProjectiveSystem.{u}

/-- The indexed clause (iii)(c) square for one site and bad place. -/
abbrev SourceTheorem311MonoThetaProjectiveSystemSquare
    {badPlace : Type u}
    (family : SourceTheorem311MonoThetaProjectiveSystemFamily badPlace)
    (n m : ℤ) (place : badPlace) :=
  SourceIndexedMonoThetaProjectiveSystemSquare
    (family.site n m place) (family.site (n + 1) m place)
    (family.common n place) (family.common (n + 1) place)

/--
The clause (iii)(d) horizontal transport for the complete Corollary 4.8(iii)
localization diagram at one absolute label.

The acting `kappa`-solvable groups, global `M_infinity^kappa` pseudo-monoids,
all local `M_infinity^kappa` pseudo-monoids, and their inclusions into
`M_infinity^(kappa times)` are retained.  This is not a square of two collapsed
profinite-group objects.
-/
structure SourceTheorem311LabeledHorizontalKummerSquare
    {l : PrimeGeFive}
    {place : Type u}
    (source target : SourceTheorem311LabeledData.{u} l place)
    (label : IUTIIAbsoluteThetaLabel.{u} l) where
  localizationHorizontal :
    SourceKappaLocalizationDiagramIso
      (source.kappaLocalization label)
      (target.kappaLocalization label)

namespace SourceTheorem311LabeledHorizontalKummerSquare

variable
    {l : PrimeGeFive}
    {place : Type u}
    {source target : SourceTheorem311LabeledData.{u} l place}
    {label : IUTIIAbsoluteThetaLabel.{u} l}

/-- The global-to-local clause (d) square at one selected place. -/
def localizationSquare
    (square :
      SourceTheorem311LabeledHorizontalKummerSquare source target label)
    (v : place) :
    SourceHorizontalKummerCompatibility
      SourceTopologicalGroupPseudoMonoidActionPair :=
  square.localizationHorizontal.localizationSquare v

/-- The local `M_infinity^kappa`-to-`M_infinity^(kappa times)` square. -/
def inclusionSquare
    (square :
      SourceTheorem311LabeledHorizontalKummerSquare source target label)
    (v : place) :
    SourceHorizontalKummerCompatibility
      SourceTopologicalGroupPseudoMonoidActionPair :=
  square.localizationHorizontal.inclusionSquare v

/-- Arbitrary automorphisms of a localization arrow transport horizontally. -/
def localizationAutomorphismEquiv
    (square :
      SourceTheorem311LabeledHorizontalKummerSquare source target label)
    (v : place) :=
  (square.localizationSquare v).automorphismEquiv

/-- Arbitrary automorphisms of a local inclusion transport horizontally. -/
def inclusionAutomorphismEquiv
    (square :
      SourceTheorem311LabeledHorizontalKummerSquare source target label)
    (v : place) :=
  (square.inclusionSquare v).automorphismEquiv

end SourceTheorem311LabeledHorizontalKummerSquare

end Iut
