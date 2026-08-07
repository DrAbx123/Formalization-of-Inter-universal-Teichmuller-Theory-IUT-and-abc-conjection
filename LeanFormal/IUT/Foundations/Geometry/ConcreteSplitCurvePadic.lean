import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitMultiplicativeCurve
import LeanFormal.IUT.Foundations.Geometry.GenericNodalReduction
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

namespace LeanFormal.IUT

noncomputable section

local instance fivePrimeFact : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev concreteLocalField := ℚ_[5]

abbrev concreteLocalIntegers := ℤ_[5]

def concreteSplitCurveLocal : WeierstrassCurve concreteLocalField :=
  WeierstrassCurve.mk 1 0 0 0 5

def concreteSplitCurveIntegral : WeierstrassCurve concreteLocalIntegers :=
  WeierstrassCurve.mk 1 0 0 0 5

theorem concreteSplitCurveIntegral_map_eq_local :
    (concreteSplitCurveIntegral.map
      (algebraMap concreteLocalIntegers concreteLocalField)) =
      concreteSplitCurveLocal := by
  rfl

theorem concreteSplitCurveLocal_map_eq_rational :
    concreteSplitCurveLocal =
      concreteSplitCurve.map (algebraMap ℚ concreteLocalField) := by
  ext <;> rfl

theorem concreteSplitCurveIntegral_is_integral :
    WeierstrassCurve.IsIntegral concreteLocalIntegers concreteSplitCurveLocal := by
  refine ⟨⟨concreteSplitCurveIntegral, ?_⟩⟩
  exact concreteSplitCurveIntegral_map_eq_local

theorem concreteSplitCurveIntegral_a₁ :
    concreteSplitCurveIntegral.a₁ = (1 : concreteLocalIntegers) := by
  rfl

theorem concreteSplitCurveIntegral_a₂ :
    concreteSplitCurveIntegral.a₂ = (0 : concreteLocalIntegers) := by
  rfl

theorem concreteSplitCurveIntegral_a₃ :
    concreteSplitCurveIntegral.a₃ = (0 : concreteLocalIntegers) := by
  rfl

theorem concreteSplitCurveIntegral_a₄ :
    concreteSplitCurveIntegral.a₄ = (0 : concreteLocalIntegers) := by
  rfl

theorem concreteSplitCurveIntegral_a₆ :
    concreteSplitCurveIntegral.a₆ = (5 : concreteLocalIntegers) := by
  rfl

theorem concreteSplitCurveIntegral_b₂ :
    concreteSplitCurveIntegral.b₂ = (1 : concreteLocalIntegers) := by
  norm_num [concreteSplitCurveIntegral, WeierstrassCurve.b₂]

theorem concreteSplitCurveIntegral_b₄ :
    concreteSplitCurveIntegral.b₄ = (0 : concreteLocalIntegers) := by
  norm_num [concreteSplitCurveIntegral, WeierstrassCurve.b₄]

theorem concreteSplitCurveIntegral_b₆ :
    concreteSplitCurveIntegral.b₆ = (20 : concreteLocalIntegers) := by
  norm_num [concreteSplitCurveIntegral, WeierstrassCurve.b₆]

theorem concreteSplitCurveIntegral_b₈ :
    concreteSplitCurveIntegral.b₈ = (5 : concreteLocalIntegers) := by
  norm_num [concreteSplitCurveIntegral, WeierstrassCurve.b₈]

theorem concreteSplitCurveIntegral_c₄ :
    concreteSplitCurveIntegral.c₄ = (1 : concreteLocalIntegers) := by
  norm_num [concreteSplitCurveIntegral, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]

theorem concreteSplitCurveIntegral_c₆ :
    concreteSplitCurveIntegral.c₆ = (-4321 : concreteLocalIntegers) := by
  norm_num [concreteSplitCurveIntegral, WeierstrassCurve.c₆,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]

theorem concreteSplitCurveIntegral_delta :
    concreteSplitCurveIntegral.Δ = (-10805 : concreteLocalIntegers) := by
  norm_num [concreteSplitCurveIntegral, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem concreteSplitCurveLocal_b₂ :
    concreteSplitCurveLocal.b₂ = (1 : concreteLocalField) := by
  norm_num [concreteSplitCurveLocal, WeierstrassCurve.b₂]

theorem concreteSplitCurveLocal_b₄ :
    concreteSplitCurveLocal.b₄ = (0 : concreteLocalField) := by
  norm_num [concreteSplitCurveLocal, WeierstrassCurve.b₄]

theorem concreteSplitCurveLocal_b₆ :
    concreteSplitCurveLocal.b₆ = (20 : concreteLocalField) := by
  norm_num [concreteSplitCurveLocal, WeierstrassCurve.b₆]

theorem concreteSplitCurveLocal_b₈ :
    concreteSplitCurveLocal.b₈ = (5 : concreteLocalField) := by
  norm_num [concreteSplitCurveLocal, WeierstrassCurve.b₈]

theorem concreteSplitCurveLocal_c₄ :
    concreteSplitCurveLocal.c₄ = (1 : concreteLocalField) := by
  norm_num [concreteSplitCurveLocal, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄]

theorem concreteSplitCurveLocal_c₆ :
    concreteSplitCurveLocal.c₆ = (-4321 : concreteLocalField) := by
  norm_num [concreteSplitCurveLocal, WeierstrassCurve.c₆,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]

theorem concreteSplitCurveLocal_delta :
    concreteSplitCurveLocal.Δ = (-10805 : concreteLocalField) := by
  norm_num [concreteSplitCurveLocal, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem concreteSplitCurveIntegral_c₄_isUnit :
    IsUnit concreteSplitCurveIntegral.c₄ := by
  rw [concreteSplitCurveIntegral_c₄]
  exact isUnit_one

theorem concreteSplitCurveIntegral_delta_mem_maximalIdeal :
    concreteSplitCurveIntegral.Δ ∈ IsLocalRing.maximalIdeal concreteLocalIntegers := by
  rw [concreteSplitCurveIntegral_delta]
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  simpa using
    (PadicInt.norm_intCast_lt_one_iff (p := 5) (z := (-10805 : ℤ))).2
      (by norm_num : (5 : ℤ) ∣ -10805)

theorem concreteSplitCurveLocal_delta_ne_zero :
    concreteSplitCurveLocal.Δ ≠ 0 := by
  rw [concreteSplitCurveLocal_delta]
  norm_num

theorem concreteSplitCurveLocal_isElliptic :
    concreteSplitCurveLocal.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  exact isUnit_iff_ne_zero.mpr concreteSplitCurveLocal_delta_ne_zero

theorem concreteSplitCurveLocal_delta_valuation_lt_one :
    (IsDiscreteValuationRing.maximalIdeal concreteLocalIntegers).valuation
      concreteLocalField concreteSplitCurveLocal.Δ < 1 := by
  rw [← concreteSplitCurveIntegral_map_eq_local]
  rw [WeierstrassCurve.map_Δ]
  change (IsDiscreteValuationRing.maximalIdeal concreteLocalIntegers).valuation
    concreteLocalField
      (algebraMap concreteLocalIntegers concreteLocalField
        concreteSplitCurveIntegral.Δ) < 1
  exact ((IsDiscreteValuationRing.maximalIdeal concreteLocalIntegers).valuation_lt_one_iff_mem
    (K := concreteLocalField) concreteSplitCurveIntegral.Δ).mpr
      concreteSplitCurveIntegral_delta_mem_maximalIdeal

theorem concreteSplitCurveLocal_c₄_valuation_eq_one :
    (IsDiscreteValuationRing.maximalIdeal concreteLocalIntegers).valuation
      concreteLocalField concreteSplitCurveLocal.c₄ = 1 := by
  rw [← concreteSplitCurveIntegral_map_eq_local]
  rw [WeierstrassCurve.map_c₄]
  exact ((IsDiscreteValuationRing.maximalIdeal concreteLocalIntegers).valuation_eq_one_iff_notMem
    (K := concreteLocalField)).mpr
      (IsLocalRing.notMem_maximalIdeal.mpr concreteSplitCurveIntegral_c₄_isUnit)

theorem concreteSplitCurveLocal_isMinimal :
    WeierstrassCurve.IsMinimal concreteLocalIntegers concreteSplitCurveLocal := by
  letI : WeierstrassCurve.IsIntegral concreteLocalIntegers concreteSplitCurveLocal :=
    concreteSplitCurveIntegral_is_integral
  exact isMinimal_of_isIntegral_valuation_c₄_eq_one
    concreteLocalIntegers concreteSplitCurveLocal
    concreteSplitCurveLocal_c₄_valuation_eq_one

theorem concreteSplitCurveLocal_hasMultiplicativeReduction :
    concreteSplitCurveLocal.HasMultiplicativeReduction concreteLocalIntegers := by
  letI : WeierstrassCurve.IsIntegral concreteLocalIntegers concreteSplitCurveLocal :=
    concreteSplitCurveIntegral_is_integral
  letI : WeierstrassCurve.IsMinimal concreteLocalIntegers concreteSplitCurveLocal :=
    concreteSplitCurveLocal_isMinimal
  exact
    { badReduction := concreteSplitCurveLocal_delta_valuation_lt_one
      multiplicativeReduction := concreteSplitCurveLocal_c₄_valuation_eq_one }

theorem concreteSplitCurveLocal_integralModel_eq_integral :
    letI : WeierstrassCurve.IsIntegral concreteLocalIntegers concreteSplitCurveLocal :=
      concreteSplitCurveIntegral_is_integral
    concreteSplitCurveLocal.integralModel concreteLocalIntegers =
      concreteSplitCurveIntegral := by
  letI : WeierstrassCurve.IsIntegral concreteLocalIntegers concreteSplitCurveLocal :=
    concreteSplitCurveIntegral_is_integral
  apply WeierstrassCurve.map_injective
    (FaithfulSMul.algebraMap_injective concreteLocalIntegers concreteLocalField)
  change
    (concreteSplitCurveLocal.integralModel concreteLocalIntegers).baseChange concreteLocalField =
      concreteSplitCurveIntegral.baseChange concreteLocalField
  rw [WeierstrassCurve.baseChange_integralModel_eq]
  exact concreteSplitCurveIntegral_map_eq_local.symm

theorem concreteSplitCurveIntegral_residue_a₁ :
    IsLocalRing.residue concreteLocalIntegers concreteSplitCurveIntegral.a₁ = 1 := by
  rw [concreteSplitCurveIntegral_a₁]
  simp

theorem concreteSplitCurveIntegral_residue_a₂ :
    IsLocalRing.residue concreteLocalIntegers concreteSplitCurveIntegral.a₂ = 0 := by
  rw [concreteSplitCurveIntegral_a₂]
  simp

theorem concreteSplitCurveIntegral_residue_a₃ :
    IsLocalRing.residue concreteLocalIntegers concreteSplitCurveIntegral.a₃ = 0 := by
  rw [concreteSplitCurveIntegral_a₃]
  simp

theorem concreteSplitCurveIntegral_residue_a₄ :
    IsLocalRing.residue concreteLocalIntegers concreteSplitCurveIntegral.a₄ = 0 := by
  rw [concreteSplitCurveIntegral_a₄]
  simp

theorem concreteSplitCurveIntegral_residue_a₆ :
    IsLocalRing.residue concreteLocalIntegers concreteSplitCurveIntegral.a₆ = 0 := by
  rw [concreteSplitCurveIntegral_a₆]
  rw [IsLocalRing.residue_eq_zero_iff]
  rw [IsLocalRing.mem_maximalIdeal]
  rw [PadicInt.mem_nonunits]
  change ‖(5 : concreteLocalIntegers)‖ < 1
  exact (PadicInt.norm_natCast_lt_one_iff (p := 5) (n := 5)).2 (by norm_num)

def concreteSplitCurveNodalData :
    NodalReductionEquation concreteLocalIntegers where
  model := concreteSplitCurveIntegral
  a₁_residue := concreteSplitCurveIntegral_residue_a₁
  a₂_residue := concreteSplitCurveIntegral_residue_a₂
  a₃_residue := concreteSplitCurveIntegral_residue_a₃
  a₄_residue := concreteSplitCurveIntegral_residue_a₄
  a₆_residue := concreteSplitCurveIntegral_residue_a₆
  b₂_residue := by
    rw [concreteSplitCurveIntegral_b₂]
    simp
  b₄_residue := by
    rw [concreteSplitCurveIntegral_b₄]
    simp
  b₆_residue := by
    rw [concreteSplitCurveIntegral_b₆]
    rw [IsLocalRing.residue_eq_zero_iff]
    rw [IsLocalRing.mem_maximalIdeal]
    rw [PadicInt.mem_nonunits]
    change ‖(20 : concreteLocalIntegers)‖ < 1
    exact (PadicInt.norm_natCast_lt_one_iff (p := 5) (n := 20)).2 (by norm_num)
  c₄_residue := by
    rw [concreteSplitCurveIntegral_c₄]
    simp

theorem concreteSplitCurveNodalData_residue_curve :
    concreteSplitCurveNodalData.residueCurve =
      NodalReductionEquation.nodalCurve (IsLocalRing.ResidueField concreteLocalIntegers) :=
  concreteSplitCurveNodalData.residueCurve_eq_nodalCurve

theorem concreteSplitCurveNodalData_tangent_splits :
    Polynomial.Splits concreteSplitCurveNodalData.tangentPolynomial :=
  concreteSplitCurveNodalData.tangentPolynomial_splits

theorem concreteSplitCurveLocal_hasSplitMultiplicativeReduction :
    concreteSplitCurveLocal.HasSplitMultiplicativeReduction concreteLocalIntegers := by
  letI : WeierstrassCurve.IsIntegral concreteLocalIntegers concreteSplitCurveLocal :=
    concreteSplitCurveIntegral_is_integral
  letI : WeierstrassCurve.IsMinimal concreteLocalIntegers concreteSplitCurveLocal :=
    concreteSplitCurveLocal_isMinimal
  letI : concreteSplitCurveLocal.HasMultiplicativeReduction concreteLocalIntegers :=
    concreteSplitCurveLocal_hasMultiplicativeReduction
  refine { splitMultiplicativeReduction := ?_ }
  rw [concreteSplitCurveLocal_integralModel_eq_integral]
  change Polynomial.Splits
    ((splitReductionPolynomial concreteSplitCurveIntegral).map
      (IsLocalRing.residue concreteLocalIntegers))
  rw [← splitReductionPolynomial_map]
  change Polynomial.Splits concreteSplitCurveNodalData.tangentPolynomial
  exact concreteSplitCurveNodalData_tangent_splits

theorem concreteSplitCurveLocal_hasStableReduction :
    concreteSplitCurveLocal.HasGoodReduction concreteLocalIntegers ∨
      concreteSplitCurveLocal.HasMultiplicativeReduction concreteLocalIntegers :=
  Or.inr concreteSplitCurveLocal_hasMultiplicativeReduction

theorem concreteSplitCurveIntegral_delta_residue :
    IsLocalRing.residue concreteLocalIntegers concreteSplitCurveIntegral.Δ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff]
  rw [IsLocalRing.mem_maximalIdeal]
  exact concreteSplitCurveIntegral_delta_mem_maximalIdeal

theorem concreteSplitCurveIntegral_c₄_residue :
    IsLocalRing.residue concreteLocalIntegers concreteSplitCurveIntegral.c₄ = 1 := by
  rw [concreteSplitCurveIntegral_c₄]
  simp

theorem concreteSplitCurveLocal_reduction_eq_nodalCurve :
    letI : WeierstrassCurve.IsMinimal concreteLocalIntegers concreteSplitCurveLocal :=
      concreteSplitCurveLocal_isMinimal
    concreteSplitCurveLocal.reduction concreteLocalIntegers =
      NodalReductionEquation.nodalCurve
        (IsLocalRing.ResidueField concreteLocalIntegers) := by
  letI : WeierstrassCurve.IsIntegral concreteLocalIntegers concreteSplitCurveLocal :=
    concreteSplitCurveIntegral_is_integral
  letI : WeierstrassCurve.IsMinimal concreteLocalIntegers concreteSplitCurveLocal :=
    concreteSplitCurveLocal_isMinimal
  rw [WeierstrassCurve.reduction, concreteSplitCurveLocal_integralModel_eq_integral]
  exact concreteSplitCurveNodalData_residue_curve

theorem concreteSplitCurveLocal_tangentPolynomial_eq_X_mul_X_add_C_one :
    concreteSplitCurveNodalData.tangentPolynomial =
      Polynomial.X *
        (Polynomial.X + Polynomial.C (1 : IsLocalRing.ResidueField concreteLocalIntegers)) :=
  concreteSplitCurveNodalData.tangentPolynomial_eq_X_mul_X_add_C_one

theorem concreteSplitCurveLocal_tangentPolynomial_monic :
    concreteSplitCurveNodalData.tangentPolynomial.Monic :=
  concreteSplitCurveNodalData.tangentPolynomial_monic

theorem concreteSplitCurveLocal_tangentPolynomial_natDegree :
    concreteSplitCurveNodalData.tangentPolynomial.natDegree = 2 :=
  concreteSplitCurveNodalData.tangentPolynomial_natDegree

theorem concreteSplitCurveLocal_tangentPolynomial_splits :
    Polynomial.Splits concreteSplitCurveNodalData.tangentPolynomial :=
  concreteSplitCurveNodalData_tangent_splits

theorem concreteSplitCurveLocal_normalizedPoint_onCurve
    (t : IsLocalRing.ResidueField concreteLocalIntegers) :
    TateCurvePadic.NodalNormalization.OnCurve
      (concreteSplitCurveNodalData.normalizedPoint t).1
      (concreteSplitCurveNodalData.normalizedPoint t).2 :=
  concreteSplitCurveNodalData.normalizedPoint_onCurve t

theorem concreteSplitCurveLocal_normalizedPoint_eq_node_iff
    (t : IsLocalRing.ResidueField concreteLocalIntegers) :
    concreteSplitCurveNodalData.normalizedPoint t = (0, 0) ↔
      t = 0 ∨ t = -1 :=
  concreteSplitCurveNodalData.normalizedPoint_eq_node_iff t

theorem concreteSplitCurveLocal_normalizedPoint_recovers_off_node
    {x y : IsLocalRing.ResidueField concreteLocalIntegers}
    (hxy : TateCurvePadic.NodalNormalization.OnCurve x y) (hx : x ≠ 0) :
    concreteSplitCurveNodalData.normalizedPoint (y / x) = (x, y) :=
  concreteSplitCurveNodalData.normalizedPoint_recovers_off_node hxy hx

structure ConcreteSplitCurveLocalCertificate where
  curve : WeierstrassCurve concreteLocalField
  integralModel : WeierstrassCurve concreteLocalIntegers
  integral : WeierstrassCurve.IsIntegral concreteLocalIntegers curve
  map_eq : integralModel.map (algebraMap concreteLocalIntegers concreteLocalField) = curve
  elliptic : curve.IsElliptic
  minimal : curve.IsMinimal concreteLocalIntegers
  multiplicative : curve.HasMultiplicativeReduction concreteLocalIntegers
  splitMultiplicative : curve.HasSplitMultiplicativeReduction concreteLocalIntegers
  reduction_eq_nodal :
    letI : WeierstrassCurve.IsMinimal concreteLocalIntegers curve := minimal
    curve.reduction concreteLocalIntegers =
      NodalReductionEquation.nodalCurve
        (IsLocalRing.ResidueField concreteLocalIntegers)
  tangent_monic : concreteSplitCurveNodalData.tangentPolynomial.Monic
  tangent_degree : concreteSplitCurveNodalData.tangentPolynomial.natDegree = 2
  tangent_splits : Polynomial.Splits concreteSplitCurveNodalData.tangentPolynomial

def concreteSplitCurveLocalCertificate : ConcreteSplitCurveLocalCertificate where
  curve := concreteSplitCurveLocal
  integralModel := concreteSplitCurveIntegral
  integral := concreteSplitCurveIntegral_is_integral
  map_eq := concreteSplitCurveIntegral_map_eq_local
  elliptic := concreteSplitCurveLocal_isElliptic
  minimal := concreteSplitCurveLocal_isMinimal
  multiplicative := concreteSplitCurveLocal_hasMultiplicativeReduction
  splitMultiplicative := concreteSplitCurveLocal_hasSplitMultiplicativeReduction
  reduction_eq_nodal := concreteSplitCurveLocal_reduction_eq_nodalCurve
  tangent_monic := concreteSplitCurveLocal_tangentPolynomial_monic
  tangent_degree := concreteSplitCurveLocal_tangentPolynomial_natDegree
  tangent_splits := concreteSplitCurveLocal_tangentPolynomial_splits

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteSplitCurvePadic : Obligation :=
  { id := "Foundations.Geometry.concrete-split-curve-padic"
    source := "IUT I, Definition 3.1(b); explicit split multiplicative local carrier"
    status := VerificationStatus.proved
    note :=
      "The explicit rational Weierstrass equation is realized over Q_5 and " ++
        "Z_5. Its integrality, nonzero discriminant, minimality, " ++
        "multiplicative reduction, nodal residue curve, and split tangent " ++
        "polynomial are proved from the actual coefficients."
    dependsOn :=
      [ "Foundations.Geometry.concrete-split-multiplicative-curve",
        "Foundations.Geometry.generic-nodal-reduction" ] }

end LeanFormal.IUT.Audit
