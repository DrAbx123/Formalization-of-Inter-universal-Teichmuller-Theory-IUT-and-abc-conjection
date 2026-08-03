import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension

/-!
  Base change of integral Weierstrass models and good reduction.

  The generic results use an explicit commuting square between the coefficient
  rings and their fraction fields. Good reduction is transported by proving
  that the discriminant of an integral model is a unit and hence remains a
  unit after applying the coefficient-ring homomorphism. The finite-place
  specialization uses the actual maps between adic completions and their
  valuation rings.
-/

namespace LeanFormal.IUT

open Polynomial

/-- An integral Weierstrass equation remains integral under a commuting square
of coefficient-ring and field homomorphisms. -/
theorem isIntegral_map_of_commutes
    {R S K L : Type*}
    [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra R K] [Algebra S L]
    (fR : R →+* S) (fK : K →+* L)
    (hcomm : fK.comp (algebraMap R K) =
      (algebraMap S L).comp fR)
    {W : WeierstrassCurve K} (hW : W.IsIntegral R) :
    (W.map fK).IsIntegral S := by
  rcases hW.integral with ⟨Wint, rfl⟩
  refine ⟨Wint.map fR, ?_⟩
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  rw [hcomm]

/-- The quadratic tangent-cone polynomial used by Mathlib's split
multiplicative reduction predicate. -/
noncomputable def splitReductionPolynomial {R : Type*} [CommRing R]
    (I : WeierstrassCurve R) : R[X] :=
  C I.c₄ * X ^ 2 + C (I.a₁ * I.c₄) * X -
    C (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)

@[simp]
theorem splitReductionPolynomial_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : WeierstrassCurve R) :
    splitReductionPolynomial (I.map f) =
      (splitReductionPolynomial I).map f := by
  simp [splitReductionPolynomial, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_b₂,
    WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
    WeierstrassCurve.map_c₄, map_ofNat]

/-- Integral models are unique after an injective algebra map, so a commuting
square identifies the chosen target model with the mapped source model. -/
theorem integralModel_map_eq_of_commutes
    {R S K L : Type*}
    [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra R K] [Algebra S L] [FaithfulSMul S L]
    (fR : R →+* S) (fK : K →+* L)
    (hcomm : fK.comp (algebraMap R K) =
      (algebraMap S L).comp fR)
    (W : WeierstrassCurve K)
    [hW : W.IsIntegral R] [hmap : (W.map fK).IsIntegral S] :
    (W.map fK).integralModel S = (W.integralModel R).map fR := by
  apply WeierstrassCurve.map_injective
    (FaithfulSMul.algebraMap_injective S L)
  change
    ((W.map fK).integralModel S).baseChange L =
      ((W.integralModel R).map fR).baseChange L
  rw [WeierstrassCurve.baseChange_integralModel_eq S (W.map fK)]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  rw [← hcomm, ← WeierstrassCurve.map_map]
  change W.map fK = ((W.integralModel R).baseChange K).map fK
  rw [WeierstrassCurve.baseChange_integralModel_eq R W]

/-- The quotient maps to residue fields commute with a local homomorphism. -/
theorem residue_comp_commutes
    {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] :
    (algebraMap S (IsLocalRing.ResidueField S)).comp f =
      (IsLocalRing.ResidueField.map f).comp
        (algebraMap R (IsLocalRing.ResidueField R)) := by
  apply RingHom.ext
  intro x
  exact (IsLocalRing.ResidueField.map_residue f x).symm

/-- The split-reduction polynomial commutes with the induced residue-field
map. -/
theorem splitReductionPolynomial_map_residue
    {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (I : WeierstrassCurve R) :
    (splitReductionPolynomial (I.map f)).map
        (algebraMap S (IsLocalRing.ResidueField S)) =
      ((splitReductionPolynomial I).map
          (algebraMap R (IsLocalRing.ResidueField R))).map
        (IsLocalRing.ResidueField.map f) := by
  rw [splitReductionPolynomial_map, Polynomial.map_map,
    Polynomial.map_map, residue_comp_commutes f]

/-- An integral equation whose discriminant has valuation one is already
minimal. This exposes the elementary lower bound used by good-reduction base
change instead of appealing to a chosen minimal model. -/
theorem isMinimal_of_isIntegral_valuation_Δ_eq_one
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [hW : W.IsIntegral R]
    (hΔ : (IsDiscreteValuationRing.maximalIdeal R).valuation K W.Δ = 1) :
    W.IsMinimal R where
  val_Δ_maximal := by
    constructor
    · simpa
    · intro C hC _
      haveI : (C • W).IsIntegral R := hC
      simp only [one_smul]
      change
        (WeierstrassCurve.valuation_Δ_aux R (C • W)).1 ≤
          (WeierstrassCurve.valuation_Δ_aux R W).1
      rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R W, hΔ]
      exact (WeierstrassCurve.valuation_Δ_aux R (C • W)).property

/-- An integral equation with unit `c₄` is minimal. Integrality after a
variable change bounds the fourth power of its scaling parameter; the
twelfth-power discriminant formula then proves discriminant maximality. -/
theorem isMinimal_of_isIntegral_valuation_c₄_eq_one
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [hW : W.IsIntegral R]
    (hc₄ : (IsDiscreteValuationRing.maximalIdeal R).valuation K W.c₄ = 1) :
    W.IsMinimal R where
  val_Δ_maximal := by
    constructor
    · simpa
    · intro C hC _
      haveI : (C • W).IsIntegral R := hC
      have hc₄le :
          (IsDiscreteValuationRing.maximalIdeal R).valuation K (C • W).c₄ ≤ 1 := by
        rw [← WeierstrassCurve.integralModel_c₄_eq R (C • W)]
        exact (IsDiscreteValuationRing.maximalIdeal R).valuation_le_one _
      rw [WeierstrassCurve.variableChange_c₄, map_mul, map_pow, hc₄, mul_one] at hc₄le
      have hu :
          (IsDiscreteValuationRing.maximalIdeal R).valuation K (↑C.u⁻¹ : K) ≤ 1 :=
        (pow_le_one_iff_of_nonneg bot_le (by norm_num : (4 : ℕ) ≠ 0)).mp hc₄le
      have hu12 :
          (IsDiscreteValuationRing.maximalIdeal R).valuation K (↑C.u⁻¹ : K) ^ 12 ≤ 1 :=
        pow_le_one₀ bot_le hu
      simp only [one_smul]
      change
        (WeierstrassCurve.valuation_Δ_aux R (C • W)).1 ≤
          (WeierstrassCurve.valuation_Δ_aux R W).1
      rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R (C • W),
        WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral R W,
        WeierstrassCurve.variableChange_Δ, map_mul, map_pow]
      exact mul_le_of_le_one_left bot_le hu12

/-- Good reduction is preserved by any commuting coefficient-ring/field
square. The proof transports the unit discriminant of the lower integral
model, then reconstructs minimality from valuation one. -/
theorem hasGoodReduction_map_of_commutes
    {R S K L : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    (fR : R →+* S) (fK : K →+* L)
    (hcomm : fK.comp (algebraMap R K) =
      (algebraMap S L).comp fR)
    (W : WeierstrassCurve K) (hW : W.HasGoodReduction R) :
    (W.map fK).HasGoodReduction S := by
  letI : W.HasGoodReduction R := hW
  have hInt : (W.map fK).IsIntegral S :=
    isIntegral_map_of_commutes fR fK hcomm
      (inferInstance : W.IsIntegral R)
  letI : (W.map fK).IsIntegral S := hInt
  let Wint := W.integralModel R
  have hWintUnit : IsUnit Wint.Δ := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    change Wint.Δ ∉ (IsDiscreteValuationRing.maximalIdeal R).asIdeal
    apply ((IsDiscreteValuationRing.maximalIdeal R).valuation_eq_one_iff_notMem
      (K := K)).mp
    rw [WeierstrassCurve.integralModel_Δ_eq R W]
    exact hW.goodReduction
  have hmapDelta :
      algebraMap S L ((Wint.map fR).Δ) = (W.map fK).Δ := by
    rw [WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ]
    rw [← WeierstrassCurve.integralModel_Δ_eq R W]
    exact (DFunLike.congr_fun hcomm Wint.Δ).symm
  have hΔ : (IsDiscreteValuationRing.maximalIdeal S).valuation L
      (W.map fK).Δ = 1 := by
    rw [← hmapDelta]
    apply ((IsDiscreteValuationRing.maximalIdeal S).valuation_eq_one_iff_notMem
      (K := L)).mpr
    change (Wint.map fR).Δ ∉ IsLocalRing.maximalIdeal S
    exact IsLocalRing.notMem_maximalIdeal.mpr
      (by simpa only [WeierstrassCurve.map_Δ] using hWintUnit.map fR)
  letI : (W.map fK).IsMinimal S :=
    isMinimal_of_isIntegral_valuation_Δ_eq_one S (W.map fK) hΔ
  exact { goodReduction := hΔ }

/-- Multiplicative reduction is preserved by a commuting local-ring/field
square. Locality preserves the nonunit discriminant, while the unit `c₄`
remains a unit under every ring homomorphism. -/
theorem hasMultiplicativeReduction_map_of_commutes
    {R S K L : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    (fR : R →+* S) [IsLocalHom fR] (fK : K →+* L)
    (hcomm : fK.comp (algebraMap R K) =
      (algebraMap S L).comp fR)
    (W : WeierstrassCurve K) (hW : W.HasMultiplicativeReduction R) :
    (W.map fK).HasMultiplicativeReduction S := by
  letI : W.HasMultiplicativeReduction R := hW
  have hInt : (W.map fK).IsIntegral S :=
    isIntegral_map_of_commutes fR fK hcomm
      (inferInstance : W.IsIntegral R)
  letI : (W.map fK).IsIntegral S := hInt
  let Wint := W.integralModel R
  have hWintDeltaMem : Wint.Δ ∈ IsLocalRing.maximalIdeal R := by
    change Wint.Δ ∈ (IsDiscreteValuationRing.maximalIdeal R).asIdeal
    apply ((IsDiscreteValuationRing.maximalIdeal R).valuation_lt_one_iff_mem
      (K := K) Wint.Δ).mp
    dsimp only [Wint]
    change (IsDiscreteValuationRing.maximalIdeal R).valuation K
      (algebraMap R K (W.integralModel R).Δ) < 1
    rw [WeierstrassCurve.integralModel_Δ_eq R W]
    exact hW.badReduction
  have hWintC4Unit : IsUnit Wint.c₄ := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    change Wint.c₄ ∉ (IsDiscreteValuationRing.maximalIdeal R).asIdeal
    apply ((IsDiscreteValuationRing.maximalIdeal R).valuation_eq_one_iff_notMem
      (K := K)).mp
    dsimp only [Wint]
    rw [WeierstrassCurve.integralModel_c₄_eq R W]
    exact hW.multiplicativeReduction
  have hmapDelta :
      algebraMap S L ((Wint.map fR).Δ) = (W.map fK).Δ := by
    rw [WeierstrassCurve.map_Δ, WeierstrassCurve.map_Δ]
    rw [← WeierstrassCurve.integralModel_Δ_eq R W]
    exact (DFunLike.congr_fun hcomm Wint.Δ).symm
  have hmapC4 :
      algebraMap S L ((Wint.map fR).c₄) = (W.map fK).c₄ := by
    rw [WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₄]
    rw [← WeierstrassCurve.integralModel_c₄_eq R W]
    exact (DFunLike.congr_fun hcomm Wint.c₄).symm
  have hDeltaMem : (Wint.map fR).Δ ∈ IsLocalRing.maximalIdeal S := by
    simpa only [WeierstrassCurve.map_Δ] using
      map_nonunit fR Wint.Δ hWintDeltaMem
  have hC4Unit : IsUnit (Wint.map fR).c₄ := by
    simpa only [WeierstrassCurve.map_c₄] using hWintC4Unit.map fR
  have hbad : (IsDiscreteValuationRing.maximalIdeal S).valuation L
      (W.map fK).Δ < 1 := by
    rw [← hmapDelta]
    exact ((IsDiscreteValuationRing.maximalIdeal S).valuation_lt_one_iff_mem
      (K := L) (Wint.map fR).Δ).mpr hDeltaMem
  have hc4 : (IsDiscreteValuationRing.maximalIdeal S).valuation L
      (W.map fK).c₄ = 1 := by
    rw [← hmapC4]
    apply ((IsDiscreteValuationRing.maximalIdeal S).valuation_eq_one_iff_notMem
      (K := L)).mpr
    change (Wint.map fR).c₄ ∉ IsLocalRing.maximalIdeal S
    exact IsLocalRing.notMem_maximalIdeal.mpr hC4Unit
  letI : (W.map fK).IsMinimal S :=
    isMinimal_of_isIntegral_valuation_c₄_eq_one S (W.map fK) hc4
  exact { badReduction := hbad, multiplicativeReduction := hc4 }

/-- Reduction of minimal models commutes with a local coefficient-ring map
and its induced residue-field map. -/
theorem reduction_map_eq_of_commutes
    {R S K L : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    (fR : R →+* S) [IsLocalHom fR] (fK : K →+* L)
    (hcomm : fK.comp (algebraMap R K) =
      (algebraMap S L).comp fR)
    (W : WeierstrassCurve K)
    [W.IsMinimal R] [(W.map fK).IsMinimal S] :
    (W.reduction R).map (IsLocalRing.ResidueField.map fR) =
      (W.map fK).reduction S := by
  have hI : (W.map fK).integralModel S = (W.integralModel R).map fR :=
    integralModel_map_eq_of_commutes fR fK hcomm W
  simp only [WeierstrassCurve.reduction]
  rw [hI, WeierstrassCurve.map_map, WeierstrassCurve.map_map]
  congr 1

/-- Split multiplicative reduction is preserved by mapping its multiplicative
reduction data and then mapping the split tangent-cone polynomial through the
induced residue-field homomorphism. -/
theorem hasSplitMultiplicativeReduction_map_of_commutes
    {R S K L : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    (fR : R →+* S) [IsLocalHom fR] (fK : K →+* L)
    (hcomm : fK.comp (algebraMap R K) =
      (algebraMap S L).comp fR)
    (W : WeierstrassCurve K) (hW : W.HasSplitMultiplicativeReduction R) :
    (W.map fK).HasSplitMultiplicativeReduction S := by
  letI : W.HasSplitMultiplicativeReduction R := hW
  have hmul : (W.map fK).HasMultiplicativeReduction S :=
    hasMultiplicativeReduction_map_of_commutes fR fK hcomm W
      hW.toHasMultiplicativeReduction
  letI : (W.map fK).HasMultiplicativeReduction S := hmul
  have hI : (W.map fK).integralModel S = (W.integralModel R).map fR :=
    integralModel_map_eq_of_commutes fR fK hcomm W
  have hs : Splits <|
      (splitReductionPolynomial (W.integralModel R)).map
        (algebraMap R (IsLocalRing.ResidueField R)) := by
    simpa only [splitReductionPolynomial] using hW.splitMultiplicativeReduction
  refine ⟨?_⟩
  change Splits <|
    (splitReductionPolynomial ((W.map fK).integralModel S)).map
      (algebraMap S (IsLocalRing.ResidueField S))
  rw [hI, splitReductionPolynomial_map_residue]
  exact hs.map (IsLocalRing.ResidueField.map fR)

/-- Presentation-independent good reduction is preserved by a commuting
coefficient-ring/field square. -/
theorem hasGoodReductionOnMinimalModel_map_of_commutes
    {R S K L : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    (fR : R →+* S) (fK : K →+* L)
    (hcomm : fK.comp (algebraMap R K) =
      (algebraMap S L).comp fR)
    (W : WeierstrassCurve K)
    (hW : HasGoodReductionOnMinimalModel R W) :
    HasGoodReductionOnMinimalModel S (W.map fK) := by
  rcases hW with ⟨C, hC⟩
  refine ⟨C.map fK, ?_⟩
  rw [WeierstrassCurve.map_variableChange]
  exact hasGoodReduction_map_of_commutes fR fK hcomm (C • W) hC

/-- Presentation-independent multiplicative reduction is preserved by a
commuting local-ring/field square. -/
theorem hasMultiplicativeReductionOnMinimalModel_map_of_commutes
    {R S K L : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    (fR : R →+* S) [IsLocalHom fR] (fK : K →+* L)
    (hcomm : fK.comp (algebraMap R K) =
      (algebraMap S L).comp fR)
    (W : WeierstrassCurve K)
    (hW : HasMultiplicativeReductionOnMinimalModel R W) :
    HasMultiplicativeReductionOnMinimalModel S (W.map fK) := by
  rcases hW with ⟨C, hC⟩
  refine ⟨C.map fK, ?_⟩
  rw [WeierstrassCurve.map_variableChange]
  exact hasMultiplicativeReduction_map_of_commutes fR fK hcomm (C • W) hC

/-- Presentation-independent split multiplicative reduction is preserved by
a commuting local-ring/field square. -/
theorem hasSplitMultiplicativeReductionOnMinimalModel_map_of_commutes
    {R S K L : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    (fR : R →+* S) [IsLocalHom fR] (fK : K →+* L)
    (hcomm : fK.comp (algebraMap R K) =
      (algebraMap S L).comp fR)
    (W : WeierstrassCurve K)
    (hW : HasSplitMultiplicativeReductionOnMinimalModel R W) :
    HasSplitMultiplicativeReductionOnMinimalModel S (W.map fK) := by
  rcases hW with ⟨C, hC⟩
  refine ⟨C.map fK, ?_⟩
  rw [WeierstrassCurve.map_variableChange]
  exact hasSplitMultiplicativeReduction_map_of_commutes fR fK hcomm (C • W) hC

namespace NumberFieldFinitePlace

universe u v

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K]
  [Algebra k K]

/-- Good reduction of a local equation is preserved by the actual embedding
`k_v -> K_w` attached to an upper finite place. -/
theorem hasGoodReductionOnMinimalModel_completionMap
    (place : NumberField.FinitePlace K)
    (W : WeierstrassCurve
      ((comap (k := k) place).maximalIdeal.adicCompletion k))
    (hW : HasGoodReductionOnMinimalModel
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) W) :
    HasGoodReductionOnMinimalModel
      (place.maximalIdeal.adicCompletionIntegers K)
      (W.map (completionMap (k := k) place)) :=
  hasGoodReductionOnMinimalModel_map_of_commutes
    (completionIntegersMap (k := k) place)
    (completionMap (k := k) place)
    (completionMap_comp_algebraMap (k := k) place) W hW

/-- Multiplicative reduction of a local equation is preserved by the actual
embedding `k_v -> K_w`. -/
theorem hasMultiplicativeReductionOnMinimalModel_completionMap
    (place : NumberField.FinitePlace K)
    (W : WeierstrassCurve
      ((comap (k := k) place).maximalIdeal.adicCompletion k))
    (hW : HasMultiplicativeReductionOnMinimalModel
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) W) :
    HasMultiplicativeReductionOnMinimalModel
      (place.maximalIdeal.adicCompletionIntegers K)
      (W.map (completionMap (k := k) place)) := by
  letI : IsLocalHom (completionIntegersMap (k := k) place) :=
    isLocalHom_completionIntegersMap place
  exact hasMultiplicativeReductionOnMinimalModel_map_of_commutes
    (completionIntegersMap (k := k) place)
    (completionMap (k := k) place)
    (completionMap_comp_algebraMap (k := k) place) W hW

/-- Split multiplicative reduction of a local equation is preserved by the
actual finite-place completion and residue-field embeddings. -/
theorem hasSplitMultiplicativeReductionOnMinimalModel_completionMap
    (place : NumberField.FinitePlace K)
    (W : WeierstrassCurve
      ((comap (k := k) place).maximalIdeal.adicCompletion k))
    (hW : HasSplitMultiplicativeReductionOnMinimalModel
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k) W) :
    HasSplitMultiplicativeReductionOnMinimalModel
      (place.maximalIdeal.adicCompletionIntegers K)
      (W.map (completionMap (k := k) place)) := by
  letI : IsLocalHom (completionIntegersMap (k := k) place) :=
    isLocalHom_completionIntegersMap place
  exact hasSplitMultiplicativeReductionOnMinimalModel_map_of_commutes
    (completionIntegersMap (k := k) place)
    (completionMap (k := k) place)
    (completionMap_comp_algebraMap (k := k) place) W hW

/-- For a global Weierstrass curve, good reduction at the contracted place is
preserved at the chosen upper place. -/
theorem hasGoodReductionOnMinimalModel_baseChange
    (place : NumberField.FinitePlace K) (W : WeierstrassCurve k)
    (hW : HasGoodReductionOnMinimalModel
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (W.baseChange
        ((comap (k := k) place).maximalIdeal.adicCompletion k))) :
    HasGoodReductionOnMinimalModel
      (place.maximalIdeal.adicCompletionIntegers K)
      (W.baseChange (place.maximalIdeal.adicCompletion K)) := by
  have hmap := hasGoodReductionOnMinimalModel_completionMap place
    (W.baseChange
      ((comap (k := k) place).maximalIdeal.adicCompletion k)) hW
  convert hmap using 1
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  apply RingHom.ext
  intro x
  exact (completionMap_coe place x).symm

/-- For a global Weierstrass curve, multiplicative reduction at the contracted
place is preserved at the chosen upper place. -/
theorem hasMultiplicativeReductionOnMinimalModel_baseChange
    (place : NumberField.FinitePlace K) (W : WeierstrassCurve k)
    (hW : HasMultiplicativeReductionOnMinimalModel
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (W.baseChange
        ((comap (k := k) place).maximalIdeal.adicCompletion k))) :
    HasMultiplicativeReductionOnMinimalModel
      (place.maximalIdeal.adicCompletionIntegers K)
      (W.baseChange (place.maximalIdeal.adicCompletion K)) := by
  have hmap := hasMultiplicativeReductionOnMinimalModel_completionMap place
    (W.baseChange
      ((comap (k := k) place).maximalIdeal.adicCompletion k)) hW
  convert hmap using 1
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  apply RingHom.ext
  intro x
  exact (completionMap_coe place x).symm

/-- For a global Weierstrass curve, split multiplicative reduction at the
contracted place is preserved at the chosen upper place. -/
theorem hasSplitMultiplicativeReductionOnMinimalModel_baseChange
    (place : NumberField.FinitePlace K) (W : WeierstrassCurve k)
    (hW : HasSplitMultiplicativeReductionOnMinimalModel
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (W.baseChange
        ((comap (k := k) place).maximalIdeal.adicCompletion k))) :
    HasSplitMultiplicativeReductionOnMinimalModel
      (place.maximalIdeal.adicCompletionIntegers K)
      (W.baseChange (place.maximalIdeal.adicCompletion K)) := by
  have hmap := hasSplitMultiplicativeReductionOnMinimalModel_completionMap place
    (W.baseChange
      ((comap (k := k) place).maximalIdeal.adicCompletion k)) hW
  convert hmap using 1
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  apply RingHom.ext
  intro x
  exact (completionMap_coe place x).symm

end NumberFieldFinitePlace

namespace PuncturedEllipticCurve

universe u v

/-- Base changing a punctured curve to a number-field extension and then to an
upper completion gives the direct base change of its underlying curve. -/
@[simp]
theorem baseChange_curve_adicCompletion
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (X : PuncturedEllipticCurve k) (place : NumberField.FinitePlace K) :
    (X.baseChange K).curve.baseChange
        (place.maximalIdeal.adicCompletion K) =
      X.curve.baseChange (place.maximalIdeal.adicCompletion K) := by
  simp only [baseChange_curve, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_map]
  congr 1

/-- Good reduction at a contracted finite place passes to the base-changed
punctured curve at the upper place. -/
theorem hasGoodReductionAt_baseChange
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (X : PuncturedEllipticCurve k) (place : NumberField.FinitePlace K)
    (hX : X.HasGoodReductionAt
      (NumberFieldFinitePlace.comap (k := k) place)) :
    (X.baseChange K).HasGoodReductionAt place := by
  change HasGoodReductionOnMinimalModel
    (place.maximalIdeal.adicCompletionIntegers K)
    ((X.baseChange K).curve.baseChange
      (place.maximalIdeal.adicCompletion K))
  rw [baseChange_curve_adicCompletion]
  exact NumberFieldFinitePlace.hasGoodReductionOnMinimalModel_baseChange
    place X.curve hX

/-- Multiplicative reduction passes to the base-changed punctured curve. -/
theorem hasMultiplicativeReductionAt_baseChange
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (X : PuncturedEllipticCurve k) (place : NumberField.FinitePlace K)
    (hX : X.HasMultiplicativeReductionAt
      (NumberFieldFinitePlace.comap (k := k) place)) :
    (X.baseChange K).HasMultiplicativeReductionAt place := by
  change HasMultiplicativeReductionOnMinimalModel
    (place.maximalIdeal.adicCompletionIntegers K)
    ((X.baseChange K).curve.baseChange
      (place.maximalIdeal.adicCompletion K))
  rw [baseChange_curve_adicCompletion]
  exact NumberFieldFinitePlace.hasMultiplicativeReductionOnMinimalModel_baseChange
    place X.curve hX

/-- Split multiplicative reduction passes through the actual residue-field
embedding to the base-changed punctured curve. -/
theorem hasSplitMultiplicativeReductionAt_baseChange
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (X : PuncturedEllipticCurve k) (place : NumberField.FinitePlace K)
    (hX : X.HasSplitMultiplicativeReductionAt
      (NumberFieldFinitePlace.comap (k := k) place)) :
    (X.baseChange K).HasSplitMultiplicativeReductionAt place := by
  change HasSplitMultiplicativeReductionOnMinimalModel
    (place.maximalIdeal.adicCompletionIntegers K)
    ((X.baseChange K).curve.baseChange
      (place.maximalIdeal.adicCompletion K))
  rw [baseChange_curve_adicCompletion]
  exact NumberFieldFinitePlace.hasSplitMultiplicativeReductionOnMinimalModel_baseChange
    place X.curve hX

/-- Stable reduction passes to every upper finite place. -/
theorem hasStableReductionAt_baseChange
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (X : PuncturedEllipticCurve k) (place : NumberField.FinitePlace K)
    (hX : X.HasStableReductionAt
      (NumberFieldFinitePlace.comap (k := k) place)) :
    (X.baseChange K).HasStableReductionAt place := by
  rcases hX with hgood | hmult
  · exact Or.inl (hasGoodReductionAt_baseChange X place hgood)
  · exact Or.inr (hasMultiplicativeReductionAt_baseChange X place hmult)

/-- Stable reduction everywhere is preserved by number-field base change. -/
theorem hasStableReductionEverywhere_baseChange
    {k : Type u} {K : Type v}
    [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K]
    (X : PuncturedEllipticCurve k)
    (hX : X.HasStableReductionEverywhere) :
    (X.baseChange K).HasStableReductionEverywhere :=
  fun place => hasStableReductionAt_baseChange X place
    (hX (NumberFieldFinitePlace.comap (k := k) place))

end PuncturedEllipticCurve

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def ellipticReductionBaseChange : Obligation :=
  { id := "Foundations.Geometry.elliptic-reduction-base-change"
    source := "Standard base change of integral Weierstrass models and good reduction"
    status := VerificationStatus.proved
    note :=
      "A commuting coefficient-ring/field square transports integral " ++
        "Weierstrass models. An integral model with unit discriminant is " ++
        "proved minimal from Mathlib's valuation definition, and good " ++
        "reduction is preserved. The result is specialized to the actual " ++
        "completion and valuation-ring maps at an upper number-field finite " ++
        "place. Multiplicative reduction is also preserved by using locality " ++
        "to transport the nonunit discriminant and the unit c4 criterion. " ++
        "The induced residue-field embedding maps the tangent-cone " ++
        "polynomial and preserves its splitting, yielding split " ++
        "multiplicative reduction as well. These preservation theorems are " ++
        "lifted to the genuine base change of a punctured elliptic curve, " ++
        "including stable reduction everywhere."
    dependsOn :=
      [ "Foundations.NumberField.finite-place-extension",
        "Foundations.Geometry.elliptic-local-reduction" ] }

end LeanFormal.IUT.Audit
