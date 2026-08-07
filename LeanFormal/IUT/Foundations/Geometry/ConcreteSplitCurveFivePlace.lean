import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurvePadic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Tactic

namespace LeanFormal.IUT

noncomputable section

def concreteFivePrime : Nat.Primes :=
  ⟨5, Nat.prime_five⟩

def concreteFiveHeightOne :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm
    concreteFivePrime

def concreteFivePlace : NumberField.FinitePlace ℚ :=
  NumberField.FinitePlace.mk concreteFiveHeightOne

@[simp] theorem concreteFivePlace_maximalIdeal :
    concreteFivePlace.maximalIdeal = concreteFiveHeightOne := by
  exact NumberField.FinitePlace.maximalIdeal_mk concreteFiveHeightOne

@[simp] theorem concreteFivePlace_underlyingPrime :
    NumberFieldFinitePlace.underlyingPrime concreteFivePlace = concreteFiveHeightOne := by
  exact concreteFivePlace_maximalIdeal

theorem concreteFiveHeightOne_natGenerator :
    Rat.HeightOneSpectrum.natGenerator concreteFiveHeightOne = 5 := by
  exact congrArg (fun p : Nat.Primes => p.1)
    ((Rat.HeightOneSpectrum.primesEquiv
      (R := NumberField.RingOfIntegers ℚ)).apply_symm_apply concreteFivePrime)

theorem concreteFiveHeightOne_five_mem :
    (5 : NumberField.RingOfIntegers ℚ) ∈ concreteFiveHeightOne.asIdeal := by
  apply (Ideal.apply_mem_of_equiv_iff
    (I := concreteFiveHeightOne.asIdeal)
    (f := Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))).mp
  have hdiv : Rat.HeightOneSpectrum.natGenerator concreteFiveHeightOne ∣ 5 := by
    rw [concreteFiveHeightOne_natGenerator]
  have hmap :=
    (Rat.HeightOneSpectrum.natGenerator_dvd_iff concreteFiveHeightOne).mp hdiv
  convert hmap using 1
  rw [Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv]
  exact map_intCast Rat.ringOfIntegersEquiv 5

abbrev concreteFiveCompletion := concreteFiveHeightOne.adicCompletion ℚ

abbrev concreteFiveCompletionIntegers :=
  concreteFiveHeightOne.adicCompletionIntegers ℚ

noncomputable def concreteFivePadicEquiv :
    concreteLocalField ≃A[ℚ] concreteFiveCompletion :=
  Padic.adicCompletionEquiv (R := NumberField.RingOfIntegers ℚ)
    concreteFivePrime

noncomputable def concreteFivePadicIntEquiv :
    concreteLocalIntegers ≃A[ℤ] concreteFiveCompletionIntegers :=
  PadicInt.adicCompletionIntegersEquiv (R := NumberField.RingOfIntegers ℚ)
    concreteFivePrime

theorem concreteFivePadicEquiv_algebraMap (x : ℚ) :
    concreteFivePadicEquiv
        (algebraMap ℚ concreteLocalField x) =
      algebraMap ℚ concreteFiveCompletion x := by
  exact concreteFivePadicEquiv.commutes x

theorem concreteFivePadicIntEquiv_coe (x : concreteLocalIntegers) :
    (concreteFivePadicIntEquiv x : concreteFiveCompletion) =
      concreteFivePadicEquiv (x : concreteLocalField) := by
  exact PadicInt.coe_adicCompletionIntegersEquiv_apply
    (R := NumberField.RingOfIntegers ℚ) concreteFivePrime x

def concreteSplitCurveAtFive : WeierstrassCurve concreteFiveCompletion :=
  concreteSplitCurve.baseChange concreteFiveCompletion

theorem concreteSplitCurveLocal_map_to_fiveCompletion :
    concreteSplitCurveLocal.map concreteFivePadicEquiv.toRingEquiv.toRingHom =
      concreteSplitCurveAtFive := by
  ext <;> simp [concreteSplitCurveLocal, concreteSplitCurveAtFive,
    concreteSplitCurve, WeierstrassCurve.baseChange]
  simpa using congrArg (fun z : concreteFiveCompletion => z.toCompletion)
    (concreteFivePadicEquiv_algebraMap 5)

theorem concreteSplitCurveAtFive_hasSplitMultiplicativeReduction :
    HasSplitMultiplicativeReductionOnMinimalModel
      concreteFiveCompletionIntegers concreteSplitCurveAtFive := by
  rw [← concreteSplitCurveLocal_map_to_fiveCompletion]
  letI : IsLocalHom concreteFivePadicIntEquiv.toRingEquiv.toRingHom := by
    refine ⟨fun x hx => ?_⟩
    simpa using hx.map concreteFivePadicIntEquiv.toRingEquiv.symm.toMonoidHom
  exact hasSplitMultiplicativeReductionOnMinimalModel_map_of_commutes
    concreteFivePadicIntEquiv.toRingEquiv.toRingHom
    concreteFivePadicEquiv.toRingEquiv.toRingHom
    (by
      apply RingHom.ext
      intro x
      change concreteFivePadicEquiv (algebraMap concreteLocalIntegers
        concreteLocalField x) =
        algebraMap concreteFiveCompletionIntegers concreteFiveCompletion
          (concreteFivePadicIntEquiv x)
      change concreteFivePadicEquiv (algebraMap concreteLocalIntegers
        concreteLocalField x) = (concreteFivePadicIntEquiv x : concreteFiveCompletion)
      rw [concreteFivePadicIntEquiv_coe]
      congr 1)
    concreteSplitCurveLocal
    ⟨1, by simpa using concreteSplitCurveLocal_hasSplitMultiplicativeReduction⟩

theorem concreteSplitCurveAtFive_hasMultiplicativeReduction :
    HasMultiplicativeReductionOnMinimalModel
      concreteFiveCompletionIntegers concreteSplitCurveAtFive := by
  rcases concreteSplitCurveAtFive_hasSplitMultiplicativeReduction with ⟨C, hC⟩
  exact ⟨C, hC.toHasMultiplicativeReduction⟩

theorem transport_splitMultiplicativeReduction_along_heightOne_eq
    {v w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}
    (F : ∀ z, WeierstrassCurve (z.adicCompletion ℚ))
    (hvw : v = w)
    (hF : HasSplitMultiplicativeReductionOnMinimalModel
      (v.adicCompletionIntegers ℚ) (F v)) :
    HasSplitMultiplicativeReductionOnMinimalModel
      (w.adicCompletionIntegers ℚ) (F w) := by
  subst w
  exact hF

theorem concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_five :
    concreteSplitPuncturedCurve.HasSplitMultiplicativeReductionAt
      concreteFivePlace := by
  unfold PuncturedEllipticCurve.HasSplitMultiplicativeReductionAt
  let F : ∀ z : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ), WeierstrassCurve (z.adicCompletion ℚ) :=
    fun z => concreteSplitCurve.baseChange (z.adicCompletion ℚ)
  have htransport :=
    transport_splitMultiplicativeReduction_along_heightOne_eq F
      concreteFivePlace_underlyingPrime.symm
      (by
        change HasSplitMultiplicativeReductionOnMinimalModel
          concreteFiveCompletionIntegers concreteSplitCurveAtFive
        exact concreteSplitCurveAtFive_hasSplitMultiplicativeReduction)
  simpa [F, concreteSplitPuncturedCurve] using htransport

theorem concreteSplitPuncturedCurve_hasMultiplicativeReductionAt_five :
    concreteSplitPuncturedCurve.HasMultiplicativeReductionAt concreteFivePlace := by
  exact PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_imp_multiplicative
    concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_five

theorem concreteSplitPuncturedCurve_hasStableReductionAt_five :
    concreteSplitPuncturedCurve.HasStableReductionAt concreteFivePlace :=
  Or.inr concreteSplitPuncturedCurve_hasMultiplicativeReductionAt_five

structure ConcreteSplitCurveFivePlaceCertificate where
  place : NumberField.FinitePlace ℚ
  place_eq : place = concreteFivePlace
  completion : WeierstrassCurve concreteFiveCompletion
  completion_eq : completion = concreteSplitCurveAtFive
  splitMultiplicative :
    HasSplitMultiplicativeReductionOnMinimalModel
      concreteFiveCompletionIntegers completion
  globalSplitMultiplicative :
    concreteSplitPuncturedCurve.HasSplitMultiplicativeReductionAt concreteFivePlace

def concreteSplitCurveFivePlaceCertificate :
    ConcreteSplitCurveFivePlaceCertificate where
  place := concreteFivePlace
  place_eq := rfl
  completion := concreteSplitCurveAtFive
  completion_eq := rfl
  splitMultiplicative := concreteSplitCurveAtFive_hasSplitMultiplicativeReduction
  globalSplitMultiplicative :=
    concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_five

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteSplitCurveFivePlace : Obligation :=
  { id := "Foundations.Geometry.concrete-split-curve-five-place"
    source := "IUT I, Definition 3.1(b); rational finite place and completion"
    status := VerificationStatus.proved
    note :=
      "The selected finite place is constructed from the actual height-one " ++
        "prime corresponding to 5 under Mathlib's Q height-one/primes " ++
        "equivalence. The Q_5 local curve is transported through the actual " ++
        "adic-completion algebra equivalences, and split multiplicative " ++
        "reduction is proved for the resulting completion carrier and for " ++
        "the global punctured curve's selected-place predicate."
    dependsOn := ["Foundations.Geometry.concrete-split-curve-padic",
      "Foundations.NumberField.finite-places"] }

end LeanFormal.IUT.Audit
