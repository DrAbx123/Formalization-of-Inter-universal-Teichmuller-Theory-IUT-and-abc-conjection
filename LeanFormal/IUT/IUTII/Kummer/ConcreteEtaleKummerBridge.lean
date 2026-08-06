import LeanFormal.IUT.IUTII.Kummer.ConcreteEtaleKummerDirection

namespace LeanFormal.IUT

noncomputable section

namespace LocalIntegralMonoid

theorem qIntegerRoot_of_etale_kernel
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] (n : ℤ)
    (h : integralTateReduction l n = 0) :
    ∃ k : ℤ,
      qIntegerRoot l.value n =
        (l.value : ℤ) • qIntegerRoot l.value k := by
  have hm : n ∈ (integralTateReduction l).ker := h
  rw [integralTateReduction_kernel] at hm
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  refine ⟨k, ?_⟩
  rw [qIntegerRoot_eq_zsmul, qIntegerRoot_eq_zsmul]
  calc
    n • Additive.ofMul (qParameterGroupification l.value) =
        (k • (l.value : ℤ)) •
          Additive.ofMul (qParameterGroupification l.value) := by rw [hk]
    _ = (l.value : ℤ) •
        (k • Additive.ofMul (qParameterGroupification l.value)) := by
      rw [zsmul_eq_mul, smul_smul]
      congr 1
      exact mul_comm _ _

theorem qIntegerRoot_one_label
    (l : PrimeGeFive) [Fact (Nat.Prime l.value)] :
    qIntegerRoot l.value 1 =
      Additive.ofMul (qParameterGroupification l.value) := by
  exact qIntegerRoot_one l.value

end LocalIntegralMonoid

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteEtaleKummerBridge : Obligation :=
  { id := "IUT-II.concrete-etale-kummer-bridge"
    source := "IUT II, finite etale theta direction and local Kummer system"
    status := VerificationStatus.proved
    note :=
      "The actual compatible root system at q=p is connected to the exact " ++
        "Z/lZ Tate-direction kernel: a zero finite label is proved to be an " ++
        "l-fold integer Kummer exponent, and the label-one root is the actual " ++
        "q carrier. This is an algebraic bridge only; geometric etale descent " ++
        "and the source theta-link remain separate obligations."
    dependsOn :=
      [ "IUT-II.concrete-integer-kummer-direction",
        "IUT-II.etale-finite-tate-direction" ] }

end LeanFormal.IUT.Audit
