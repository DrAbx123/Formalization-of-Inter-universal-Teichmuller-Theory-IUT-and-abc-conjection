/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.InitialThetaData
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Preorder

/-!
Typed source boundary for the Hodge theaters constructed in IUT I.

This module separates two claims:

* `Stage1HodgeTheaterSource.ofInitialThetaData` constructs the typed histories,
  prime-strip ownership, bridge incidence, and `Theta^{±ell}NF` gluing boundary
  used by Stage 1.
* `ToyIUTIHodgeTheaterRealization` is a degree-preorder test double.  It is
  intentionally named as a toy and cannot discharge any paper-source
  obligation.

Thus no string label or inert identifier is an input to the canonical source
constructor, while the missing categorical construction is not silently assumed.
-/

namespace Iut

universe u

/-- The two arithmetic histories used at the Stage 1 `0`/`1`-column boundary. -/
inductive ThetaHodgeColumn where
  | zero
  | one
  deriving DecidableEq

/--
An arithmetic history belonging to one fixed collection of initial theta data.

The two constructors are distinct by construction; there is no string-valued
history label that could identify them accidentally.
-/
inductive ThetaArithmeticHistory
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K) where
  | zero
  | one
  deriving DecidableEq

namespace ThetaArithmeticHistory

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

/-- The column occupied by an arithmetic history. -/
def column : ThetaArithmeticHistory theta -> ThetaHodgeColumn
  | .zero => .zero
  | .one => .one

@[simp]
theorem zero_column : column (.zero : ThetaArithmeticHistory theta) = .zero :=
  rfl

@[simp]
theorem one_column : column (.one : ThetaArithmeticHistory theta) = .one :=
  rfl

theorem zero_ne_one :
    (ThetaArithmeticHistory.zero : ThetaArithmeticHistory theta) ≠ .one := by
  intro h
  cases h

end ThetaArithmeticHistory

/-- Roles played by prime strips in the IUT I bridge-and-gluing diagram. -/
inductive ThetaPrimeStripRole where
  | plusMinus
  | theta
  | nf
  | gluing
  deriving DecidableEq

/--
A typed prime strip owned by one arithmetic history.

The record has a unique constructor. Its mathematical content is exposed by
the projections below and is definitionally inherited from `theta`: the global
orbicurve, local orbicurves, local cusps, and bad-place q-orders are never
supplied as independent identifiers.
-/
structure ThetaPrimeStrip
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K)
    (history : ThetaArithmeticHistory theta)
    (role : ThetaPrimeStripRole) where

namespace ThetaPrimeStrip

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}
variable {history : ThetaArithmeticHistory theta}
variable {role : ThetaPrimeStripRole}

/-- The unique prime strip for the given datum, history, and role. -/
def ofInitialThetaData : ThetaPrimeStrip theta history role :=
  {}

/-- The arithmetic history that owns the prime strip. -/
def owner (_strip : ThetaPrimeStrip theta history role) :
    ThetaArithmeticHistory theta :=
  history

/-- The global orbicurve underlying the prime strip. -/
def globalOrbicurve (_strip : ThetaPrimeStrip theta history role) :
    HyperbolicOrbicurveModel K :=
  theta.coverData.cK

/-- The selected valuation set indexing the prime strip. -/
def selectedPlaces (_strip : ThetaPrimeStrip theta history role) :
    Set (ThetaPlace K) :=
  theta.valuations.selectedPlaces

/-- The local orbicurve at a selected finite place. -/
def localOrbicurve
    (_strip : ThetaPrimeStrip theta history role)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.selected) :
    HyperbolicOrbicurveModel (v.maximalIdeal.adicCompletion K) :=
  theta.badLocalData.localC v hv

/-- The cusp induced by `epsilon` at a selected finite place. -/
def localCusp
    (_strip : ThetaPrimeStrip theta history role)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.selected) :
    CuspData (theta.badLocalData.localC v hv) :=
  theta.cuspLocalData.localCusp v hv

/-- The positive q-parameter order at a selected bad place. -/
noncomputable def qParameterOrder
    (_strip : ThetaPrimeStrip theta history role)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) : ℕ :=
  theta.selectedFQParameterOrder v hv

theorem qParameterOrder_pos
    (strip : ThetaPrimeStrip theta history role)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    0 < strip.qParameterOrder v hv :=
  theta.selectedFQParameterOrder_pos v hv

theorem qParameterOrder_coprime_l
    (strip : ThetaPrimeStrip theta history role)
    (v : NumberField.FinitePlace K) (hv : v ∈ theta.valuations.bad) :
    Nat.Coprime (strip.qParameterOrder v hv) theta.l.value :=
  theta.selectedFQParameterOrder_coprime_l v hv

end ThetaPrimeStrip

/-- The three bridge shapes used to assemble a `Theta^{±ell}NF` theater. -/
inductive ThetaBridgeKind where
  | thetaPM
  | thetaEll
  | thetaNF
  deriving DecidableEq

namespace ThetaBridgeKind

/-- The source prime-strip role of a bridge. -/
def domainRole : ThetaBridgeKind -> ThetaPrimeStripRole
  | .thetaPM => .plusMinus
  | .thetaEll => .plusMinus
  | .thetaNF => .nf

/-- The target prime-strip role of a bridge. -/
def codomainRole : ThetaBridgeKind -> ThetaPrimeStripRole
  | .thetaPM => .gluing
  | .thetaEll => .theta
  | .thetaNF => .gluing

end ThetaBridgeKind

/-- A typed bridge with its domain and codomain prime strips. -/
structure ThetaBridgeSource
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K)
    (history : ThetaArithmeticHistory theta)
    (kind : ThetaBridgeKind) where
  domain : ThetaPrimeStrip theta history kind.domainRole
  codomain : ThetaPrimeStrip theta history kind.codomainRole

namespace ThetaBridgeSource

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}
variable {history : ThetaArithmeticHistory theta}

/-- Construct a bridge boundary directly from the initial theta datum. -/
def ofInitialThetaData (kind : ThetaBridgeKind) :
    ThetaBridgeSource theta history kind :=
  { domain := ThetaPrimeStrip.ofInitialThetaData,
    codomain := ThetaPrimeStrip.ofInitialThetaData }

end ThetaBridgeSource

/-- The typed `Theta^{±ell}` component of a Hodge theater. -/
structure ThetaPlusMinusEllHodgeTheater
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K)
    (history : ThetaArithmeticHistory theta) where
  thetaPMBridge : ThetaBridgeSource theta history .thetaPM
  thetaEllBridge : ThetaBridgeSource theta history .thetaEll
  commonDomain : thetaPMBridge.domain = thetaEllBridge.domain

/-- The typed `Theta^NF` component of a Hodge theater. -/
structure ThetaNFHodgeTheater
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K)
    (history : ThetaArithmeticHistory theta) where
  thetaNFBridge : ThetaBridgeSource theta history .thetaNF

/--
The gluing of the `Theta^{±ell}` and `Theta^NF` components along their
common gluing-role prime strip.
-/
structure ThetaHodgeTheaterGluing
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : InitialThetaData Fmod F K}
    {history : ThetaArithmeticHistory theta}
    (plusMinusEll : ThetaPlusMinusEllHodgeTheater theta history)
    (nf : ThetaNFHodgeTheater theta history) where
  primeStripIdentification :
    plusMinusEll.thetaPMBridge.codomain = nf.thetaNFBridge.codomain

/-- A typed `Theta^{±ell}NF` Hodge theater in one arithmetic history. -/
structure ThetaPlusMinusEllNFHodgeTheater
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K)
    (history : ThetaArithmeticHistory theta) where
  plusMinusEll : ThetaPlusMinusEllHodgeTheater theta history
  nf : ThetaNFHodgeTheater theta history
  gluing : ThetaHodgeTheaterGluing plusMinusEll nf

namespace ThetaPlusMinusEllNFHodgeTheater

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}
variable {history : ThetaArithmeticHistory theta}

/-- Construct the bridge incidence and gluing data from initial theta data. -/
def ofInitialThetaData :
    ThetaPlusMinusEllNFHodgeTheater theta history := by
  let thetaPM : ThetaBridgeSource theta history .thetaPM :=
    ThetaBridgeSource.ofInitialThetaData .thetaPM
  let thetaEll : ThetaBridgeSource theta history .thetaEll :=
    ThetaBridgeSource.ofInitialThetaData .thetaEll
  let thetaNF : ThetaBridgeSource theta history .thetaNF :=
    ThetaBridgeSource.ofInitialThetaData .thetaNF
  let plusMinusEll : ThetaPlusMinusEllHodgeTheater theta history :=
    { thetaPMBridge := thetaPM,
      thetaEllBridge := thetaEll,
      commonDomain := rfl }
  let nf : ThetaNFHodgeTheater theta history :=
    { thetaNFBridge := thetaNF }
  exact
    { plusMinusEll := plusMinusEll,
      nf := nf,
      gluing := { primeStripIdentification := rfl } }

end ThetaPlusMinusEllNFHodgeTheater

/--
The canonical typed Hodge-theater source consumed by Stage 1.

Both columns are computed from the same initial theta datum, but their history
indices are different constructors.
-/
structure Stage1HodgeTheaterSource
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K) where
  zeroColumn :
    ThetaPlusMinusEllNFHodgeTheater theta (.zero : ThetaArithmeticHistory theta)
  oneColumn :
    ThetaPlusMinusEllNFHodgeTheater theta (.one : ThetaArithmeticHistory theta)

namespace Stage1HodgeTheaterSource

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

/-- The canonical M1 constructor. -/
def ofInitialThetaData (theta : InitialThetaData Fmod F K) :
    Stage1HodgeTheaterSource theta :=
  { zeroColumn := ThetaPlusMinusEllNFHodgeTheater.ofInitialThetaData,
    oneColumn := ThetaPlusMinusEllNFHodgeTheater.ofInitialThetaData }

/-- The input prime strip is owned by the `0`-column history. -/
def inputPrimeStrip (source : Stage1HodgeTheaterSource theta) :
    ThetaPrimeStrip theta (.zero : ThetaArithmeticHistory theta) .plusMinus :=
  source.zeroColumn.plusMinusEll.thetaPMBridge.domain

/-- The output prime strip is owned by the `1`-column history. -/
def outputPrimeStrip (source : Stage1HodgeTheaterSource theta) :
    ThetaPrimeStrip theta (.one : ThetaArithmeticHistory theta) .theta :=
  source.oneColumn.plusMinusEll.thetaEllBridge.codomain

theorem histories_not_identified (_source : Stage1HodgeTheaterSource theta) :
    (ThetaArithmeticHistory.zero : ThetaArithmeticHistory theta) ≠ .one :=
  ThetaArithmeticHistory.zero_ne_one

@[simp]
theorem inputPrimeStrip_column (source : Stage1HodgeTheaterSource theta) :
    source.inputPrimeStrip.owner.column = .zero :=
  rfl

@[simp]
theorem outputPrimeStrip_column (source : Stage1HodgeTheaterSource theta) :
    source.outputPrimeStrip.owner.column = .one :=
  rfl

theorem zeroColumn_primeStrip_compatible
    (source : Stage1HodgeTheaterSource theta) :
    source.zeroColumn.plusMinusEll.thetaPMBridge.codomain =
      source.zeroColumn.nf.thetaNFBridge.codomain :=
  source.zeroColumn.gluing.primeStripIdentification

theorem oneColumn_primeStrip_compatible
    (source : Stage1HodgeTheaterSource theta) :
    source.oneColumn.plusMinusEll.thetaPMBridge.codomain =
      source.oneColumn.nf.thetaNFBridge.codomain :=
  source.oneColumn.gluing.primeStripIdentification

end Stage1HodgeTheaterSource

/--
The effective-divisor degree objects of an IUT I Frobenioid prime strip.

The history and prime-strip role are type indices, so an object cannot be
moved to another arithmetic history or strip without an explicit reindexing.
The preorder category records the Frobenioid direction in which effective
divisor degree may increase.
-/
structure ToyThetaFrobenioidObject
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K)
    (history : ThetaArithmeticHistory theta)
    (role : ThetaPrimeStripRole) where
  divisorDegree : ULift.{u} ℕ

namespace ToyThetaFrobenioidObject

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

instance (history : ThetaArithmeticHistory theta) (role : ThetaPrimeStripRole) :
    Preorder (ToyThetaFrobenioidObject theta history role) where
  le source target := source.divisorDegree.down ≤ target.divisorDegree.down
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans

/-- Reindex a degree Frobenioid across an explicitly named history/strip boundary. -/
def reindexOrderIso
    (sourceHistory targetHistory : ThetaArithmeticHistory theta)
    (sourceRole targetRole : ThetaPrimeStripRole) :
    ToyThetaFrobenioidObject theta sourceHistory sourceRole ≃o
      ToyThetaFrobenioidObject theta targetHistory targetRole where
  toFun object :=
    { divisorDegree := object.divisorDegree }
  invFun object :=
    { divisorDegree := object.divisorDegree }
  left_inv object := by cases object; rfl
  right_inv object := by cases object; rfl
  map_rel_iff' := Iff.rfl

/-- The prime-strip Frobenioid category at a typed history and role. -/
def category
    (history : ThetaArithmeticHistory theta) (role : ThetaPrimeStripRole) :
    CategoryTheory.Cat.{u, u} :=
    CategoryTheory.Cat.of (ToyThetaFrobenioidObject theta history role)

end ToyThetaFrobenioidObject

/--
The local effective-divisor degree objects at one place of one arithmetic
history.  The place remains a type index even though the current categorical
model retains only the divisor-degree coordinate.
-/
structure ToyThetaLocalFrobenioidObject
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    (theta : InitialThetaData Fmod F K)
    (history : ThetaArithmeticHistory theta)
    (place : ThetaPlace K) where
  divisorDegree : ULift.{u} ℕ

namespace ToyThetaLocalFrobenioidObject

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

instance (history : ThetaArithmeticHistory theta) (place : ThetaPlace K) :
    Preorder (ToyThetaLocalFrobenioidObject theta history place) where
  le source target := source.divisorDegree.down ≤ target.divisorDegree.down
  le_refl _ := Nat.le_refl _
  le_trans _ _ _ := Nat.le_trans

/-- The local Frobenioid category at a typed history and place. -/
def category
    (history : ThetaArithmeticHistory theta) (place : ThetaPlace K) :
    CategoryTheory.Cat.{u, u} :=
    CategoryTheory.Cat.of (ToyThetaLocalFrobenioidObject theta history place)

end ToyThetaLocalFrobenioidObject

/--
The degree-preorder test double for the typed source boundary.

This has the same broad interface shape as several local/global categories in
IUT I, but it contains only effective-divisor degrees and typed order
equivalences.  It is retained for experiments and cannot discharge Definition
3.6, Corollary 3.7, Definitions 4.1 and 5.2, Proposition 6.7, Remark 6.12.2,
or Definition 6.13.
-/
structure ToyIUTIHodgeTheaterRealization
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : InitialThetaData Fmod F K}
    (source : Stage1HodgeTheaterSource theta) where
  zeroColumnSourceGluing :
    source.zeroColumn.plusMinusEll.thetaPMBridge.codomain =
      source.zeroColumn.nf.thetaNFBridge.codomain
  oneColumnSourceGluing :
    source.oneColumn.plusMinusEll.thetaPMBridge.codomain =
      source.oneColumn.nf.thetaNFBridge.codomain
  localFrobenioid :
    ThetaArithmeticHistory theta -> ThetaPlace K -> CategoryTheory.Cat.{u, u}
  thetaFPrimeStrip :
    ThetaArithmeticHistory theta -> CategoryTheory.Cat.{u, u}
  moduliFPrimeStrip :
    ThetaArithmeticHistory theta -> CategoryTheory.Cat.{u, u}
  plusMinusEllTheater :
    ThetaArithmeticHistory theta -> CategoryTheory.Cat.{u, u}
  nfTheater :
    ThetaArithmeticHistory theta -> CategoryTheory.Cat.{u, u}
  zeroToOneThetaLink :
    CategoryTheory.Equivalence
      (thetaFPrimeStrip .zero) (moduliFPrimeStrip .one)
  plusMinusEllNFGluing :
    ∀ history,
      CategoryTheory.Equivalence
        (plusMinusEllTheater history) (nfTheater history)

namespace ToyIUTIHodgeTheaterRealization

variable {Fmod F K : Type u}
variable [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
variable [Field K] [NumberField K]
variable [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
variable [FiniteDimensional Fmod F] [IsGalois Fmod F]
variable [FiniteDimensional F K] [IsGalois F K]
variable {theta : InitialThetaData Fmod F K}

/-- Construct the explicit degree-preorder test double from the typed source. -/
def ofStage1HodgeTheaterSource
    (source : Stage1HodgeTheaterSource theta) :
    ToyIUTIHodgeTheaterRealization source where
  zeroColumnSourceGluing := source.zeroColumn_primeStrip_compatible
  oneColumnSourceGluing := source.oneColumn_primeStrip_compatible
  localFrobenioid := fun history place =>
    ToyThetaLocalFrobenioidObject.category history place
  thetaFPrimeStrip := fun history =>
    ToyThetaFrobenioidObject.category history .plusMinus
  moduliFPrimeStrip := fun history =>
    ToyThetaFrobenioidObject.category history .theta
  plusMinusEllTheater := fun history =>
    ToyThetaFrobenioidObject.category history .plusMinus
  nfTheater := fun history =>
    ToyThetaFrobenioidObject.category history .nf
  zeroToOneThetaLink :=
    (ToyThetaFrobenioidObject.reindexOrderIso
      (.zero : ThetaArithmeticHistory theta)
      (.one : ThetaArithmeticHistory theta)
      .plusMinus .theta).equivalence
  plusMinusEllNFGluing := fun history =>
    (ToyThetaFrobenioidObject.reindexOrderIso
      history history .plusMinus .nf).equivalence

end ToyIUTIHodgeTheaterRealization

/-- The realized IUT I construction predicate consumed by later stages. -/
def Stage1HodgeTheaterSource.HasToyIUTIRealization
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : InitialThetaData Fmod F K}
    (source : Stage1HodgeTheaterSource theta) : Prop :=
  Nonempty (ToyIUTIHodgeTheaterRealization source)

theorem Stage1HodgeTheaterSource.hasToyIUTIRealization
    {Fmod F K : Type u}
    [Field Fmod] [NumberField Fmod] [Field F] [NumberField F]
    [Field K] [NumberField K]
    [Algebra Fmod F] [Algebra F K] [Algebra Fmod K] [IsScalarTower Fmod F K]
    [FiniteDimensional Fmod F] [IsGalois Fmod F]
    [FiniteDimensional F K] [IsGalois F K]
    {theta : InitialThetaData Fmod F K}
    (source : Stage1HodgeTheaterSource theta) :
    source.HasToyIUTIRealization :=
  ⟨ToyIUTIHodgeTheaterRealization.ofStage1HodgeTheaterSource source⟩

end Iut
