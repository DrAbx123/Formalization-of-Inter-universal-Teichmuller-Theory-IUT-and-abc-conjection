import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
  Presentation-independent local reduction predicates for elliptic curves.

  Mathlib's reduction classes apply to a minimal Weierstrass equation.  The
  predicates below quantify over an actual variable change and therefore
  describe the represented curve rather than one stored equation.  Their
  invariance is proved before they are used to classify any number-field
  place.

  Source comparison: IUT I, Definition 3.1(b); compare the local-reduction
  block of `promachina/iut-lean/Iut/Foundations/InitialThetaData.lean`.
-/

namespace LeanFormal.IUT

def HasGoodReductionOnMinimalModel
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange K,
    (C • W).HasGoodReduction R

def HasMultiplicativeReductionOnMinimalModel
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange K,
    (C • W).HasMultiplicativeReduction R

def HasSplitMultiplicativeReductionOnMinimalModel
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange K,
    (C • W).HasSplitMultiplicativeReduction R

theorem hasGoodReductionOnMinimalModel_smul_iff
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) :
    HasGoodReductionOnMinimalModel R (C • W) ↔
      HasGoodReductionOnMinimalModel R W := by
  constructor
  · rintro ⟨D, hD⟩
    exact ⟨D * C, by simpa only [mul_smul] using hD⟩
  · rintro ⟨D, hD⟩
    exact ⟨D * C⁻¹, by simp only [mul_smul, inv_smul_smul, hD]⟩

theorem hasMultiplicativeReductionOnMinimalModel_smul_iff
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) :
    HasMultiplicativeReductionOnMinimalModel R (C • W) ↔
      HasMultiplicativeReductionOnMinimalModel R W := by
  constructor
  · rintro ⟨D, hD⟩
    exact ⟨D * C, by simpa only [mul_smul] using hD⟩
  · rintro ⟨D, hD⟩
    exact ⟨D * C⁻¹, by simp only [mul_smul, inv_smul_smul, hD]⟩

theorem hasSplitMultiplicativeReductionOnMinimalModel_smul_iff
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve K) :
    HasSplitMultiplicativeReductionOnMinimalModel R (C • W) ↔
      HasSplitMultiplicativeReductionOnMinimalModel R W := by
  constructor
  · rintro ⟨D, hD⟩
    exact ⟨D * C, by simpa only [mul_smul] using hD⟩
  · rintro ⟨D, hD⟩
    exact ⟨D * C⁻¹, by simp only [mul_smul, inv_smul_smul, hD]⟩

theorem hasGoodReductionOnMinimalModel_minimal_iff
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) :
    HasGoodReductionOnMinimalModel R (W.minimal R) ↔
      HasGoodReductionOnMinimalModel R W := by
  simpa only [WeierstrassCurve.minimal] using
    hasGoodReductionOnMinimalModel_smul_iff R
      (W.exists_isMinimal R).choose W

theorem hasMultiplicativeReductionOnMinimalModel_minimal_iff
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) :
    HasMultiplicativeReductionOnMinimalModel R (W.minimal R) ↔
      HasMultiplicativeReductionOnMinimalModel R W := by
  simpa only [WeierstrassCurve.minimal] using
    hasMultiplicativeReductionOnMinimalModel_smul_iff R
      (W.exists_isMinimal R).choose W

theorem hasSplitMultiplicativeReductionOnMinimalModel_minimal_iff
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) :
    HasSplitMultiplicativeReductionOnMinimalModel R (W.minimal R) ↔
      HasSplitMultiplicativeReductionOnMinimalModel R W := by
  simpa only [WeierstrassCurve.minimal] using
    hasSplitMultiplicativeReductionOnMinimalModel_smul_iff R
      (W.exists_isMinimal R).choose W

theorem hasGoodReductionOnMinimalModel_map_variableChange_iff
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K L : Type*} [Field K] [Field L]
    [Algebra R L] [IsFractionRing R L]
    (φ : K →+* L) (C : WeierstrassCurve.VariableChange K)
    (W : WeierstrassCurve K) :
    HasGoodReductionOnMinimalModel R ((C • W).map φ) ↔
      HasGoodReductionOnMinimalModel R (W.map φ) := by
  rw [← WeierstrassCurve.map_variableChange]
  exact hasGoodReductionOnMinimalModel_smul_iff R (C.map φ) (W.map φ)

theorem hasMultiplicativeReductionOnMinimalModel_map_variableChange_iff
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K L : Type*} [Field K] [Field L]
    [Algebra R L] [IsFractionRing R L]
    (φ : K →+* L) (C : WeierstrassCurve.VariableChange K)
    (W : WeierstrassCurve K) :
    HasMultiplicativeReductionOnMinimalModel R ((C • W).map φ) ↔
      HasMultiplicativeReductionOnMinimalModel R (W.map φ) := by
  rw [← WeierstrassCurve.map_variableChange]
  exact hasMultiplicativeReductionOnMinimalModel_smul_iff R
    (C.map φ) (W.map φ)

theorem hasSplitMultiplicativeReductionOnMinimalModel_map_variableChange_iff
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K L : Type*} [Field K] [Field L]
    [Algebra R L] [IsFractionRing R L]
    (φ : K →+* L) (C : WeierstrassCurve.VariableChange K)
    (W : WeierstrassCurve K) :
    HasSplitMultiplicativeReductionOnMinimalModel R ((C • W).map φ) ↔
      HasSplitMultiplicativeReductionOnMinimalModel R (W.map φ) := by
  rw [← WeierstrassCurve.map_variableChange]
  exact hasSplitMultiplicativeReductionOnMinimalModel_smul_iff R
    (C.map φ) (W.map φ)

namespace PuncturedEllipticCurve

noncomputable def HasGoodReductionAt
    {F : Type*} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F) (place : NumberField.FinitePlace F) : Prop :=
  let prime := NumberFieldFinitePlace.underlyingPrime place
  let localCurve := X.curve.baseChange (prime.adicCompletion F)
  HasGoodReductionOnMinimalModel
    (prime.adicCompletionIntegers F) localCurve

noncomputable def HasMultiplicativeReductionAt
    {F : Type*} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F) (place : NumberField.FinitePlace F) : Prop :=
  let prime := NumberFieldFinitePlace.underlyingPrime place
  let localCurve := X.curve.baseChange (prime.adicCompletion F)
  HasMultiplicativeReductionOnMinimalModel
    (prime.adicCompletionIntegers F) localCurve

noncomputable def HasSplitMultiplicativeReductionAt
    {F : Type*} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F) (place : NumberField.FinitePlace F) : Prop :=
  let prime := NumberFieldFinitePlace.underlyingPrime place
  let localCurve := X.curve.baseChange (prime.adicCompletion F)
  HasSplitMultiplicativeReductionOnMinimalModel
    (prime.adicCompletionIntegers F) localCurve

noncomputable def HasStableReductionAt
    {F : Type*} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F) (place : NumberField.FinitePlace F) : Prop :=
  X.HasGoodReductionAt place ∨ X.HasMultiplicativeReductionAt place

def HasStableReductionEverywhere
    {F : Type*} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F) : Prop :=
  ∀ place : NumberField.FinitePlace F, X.HasStableReductionAt place

theorem hasSplitMultiplicativeReductionAt_imp_multiplicative
    {F : Type*} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F} {place : NumberField.FinitePlace F}
    (h : X.HasSplitMultiplicativeReductionAt place) :
    X.HasMultiplicativeReductionAt place := by
  rcases h with ⟨C, hC⟩
  exact ⟨C, hC.toHasMultiplicativeReduction⟩

theorem hasGoodReductionAt_imp_stable
    {F : Type*} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F} {place : NumberField.FinitePlace F}
    (h : X.HasGoodReductionAt place) :
    X.HasStableReductionAt place :=
  Or.inl h

theorem hasMultiplicativeReductionAt_imp_stable
    {F : Type*} [Field F] [NumberField F]
    {X : PuncturedEllipticCurve F} {place : NumberField.FinitePlace F}
    (h : X.HasMultiplicativeReductionAt place) :
    X.HasStableReductionAt place :=
  Or.inr h

end PuncturedEllipticCurve

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def ellipticLocalReductionKernel : Obligation :=
  { id := "Foundations.Geometry.elliptic-local-reduction"
    source := "Mathlib elliptic-curve reduction; IUT I, Definition 3.1(b) prerequisite"
    status := VerificationStatus.proved
    note :=
      "Good, multiplicative, and split multiplicative reduction are lifted " ++
        "from minimal equations to presentation-independent curve predicates. " ++
        "Coordinate-change, chosen-minimal-model, and scalar-map invariance " ++
        "are proved, as are the split-to-multiplicative and stable-reduction " ++
        "implications. Existence at any arithmetic place is not asserted."
    dependsOn :=
      [ "Foundations.NumberField.finite-places",
        "Foundations.Geometry.punctured-elliptic-curve" ] }

def ellipticStableReductionAtPlaces : Obligation :=
  { id := "IUT-I.elliptic-stable-reduction-at-places"
    source := "IUT I, Definition 3.1(b)"
    status := VerificationStatus.interface
    note :=
      "The source-facing local and everywhere predicates are now concrete, " ++
        "using the actual number-field completion and its valuation ring. " ++
        "No theorem proves stable or split multiplicative reduction for the " ++
        "IUT input curve, and no Tate parameter is constructed."
    dependsOn := ["Foundations.Geometry.elliptic-local-reduction"] }

end LeanFormal.IUT.Audit
