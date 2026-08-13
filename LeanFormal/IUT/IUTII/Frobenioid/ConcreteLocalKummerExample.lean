import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralUnitKummer

/-!
  A concrete Kummer input for the local parameter `q = p`.

  The local-prime-place layer supplies the nontrivial parameter `p` in the
  algebraic closure of `Q_p`.  Here that same element is placed in the actual
  nonzero integral-closure monoid, then in its Grothendieck groupification, and
  the already proved divisibility theorem supplies one coherent rational-root
  system.  This is a concrete local Kummer object; it does not identify the
  object with an etale/Frobenioid theta link.
-/

namespace LeanFormal.IUT

noncomputable section

namespace LocalIntegralMonoid

variable (p : Nat) [Fact (Nat.Prime p)]

def qParameter : LocalIntegralMonoid p :=
  let pInteger : Valuation.integer (ValuativeRel.valuation ℚ_[p]) :=
    ⟨(p : ℚ_[p]), by
      rw [Valuation.mem_integer_iff]
      exact le_of_lt (Padic.valuation_p_lt_one
        (ValuativeRel.valuation ℚ_[p]))⟩
  let pIntegral : LocalAlgebraicIntegerRing p :=
    algebraMap _ _ pInteger
  ⟨pIntegral, mem_nonZeroDivisors_of_ne_zero (by
    intro h
    have hcoerce := congrArg (fun value : LocalAlgebraicIntegerRing p =>
      (value : AlgebraicClosure ℚ_[p])) h
    change (p : AlgebraicClosure ℚ_[p]) = 0 at hcoerce
    exact (Nat.cast_ne_zero.mpr
      (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))) hcoerce)⟩

@[simp] theorem toAlgebraicClosureUnits_qParameter :
    toAlgebraicClosureUnits p (qParameter p) = localQParameterFor p := by
  apply Units.ext
  rfl

def qParameterGroupification :
    Algebra.GrothendieckGroup (LocalIntegralMonoid p) :=
  Algebra.GrothendieckGroup.of (qParameter p)

theorem qParameterGroupification_maps_to_q :
    groupificationEquivAlgebraicClosureUnits p (qParameterGroupification p) =
      localQParameterFor p := by
  change groupificationToAlgebraicClosureUnits p
      (Algebra.GrothendieckGroup.of (qParameter p)) =
      localQParameterFor p
  rw [groupificationToAlgebraicClosureUnits_of,
    toAlgebraicClosureUnits_qParameter]

theorem qParameter_ne_one : qParameter p ≠ 1 := by
  intro h
  have mapped := congrArg (fun value : LocalIntegralMonoid p =>
      toAlgebraicClosureUnits p value) h
  have hq : localQParameterFor p ≠ 1 := by
    let v : RationalPrimePlace := ⟨p, Fact.out⟩
    simpa [localQParameter] using localQParameter_ne_one v
  apply hq
  simpa [toAlgebraicClosureUnits_qParameter] using mapped

theorem qParameterGroupification_ne_one :
    qParameterGroupification p ≠ 1 := by
  intro h
  have mapped := congrArg (groupificationEquivAlgebraicClosureUnits p) h
  have hq : localQParameterFor p ≠ 1 := by
    let v : RationalPrimePlace := ⟨p, Fact.out⟩
    simpa [localQParameter] using localQParameter_ne_one v
  apply hq
  rw [qParameterGroupification_maps_to_q, map_one] at mapped
  exact mapped

noncomputable def qParameterCompatibleRoots :
    CompatibleRootSystem
      (Algebra.GrothendieckGroup (LocalIntegralMonoid p))
      (qParameterGroupification p) :=
  groupificationCompatibleRoots p (qParameterGroupification p)

theorem qParameterCompatibleRoots_at_one :
    (qParameterCompatibleRoots p).roots 1 =
      Additive.ofMul (qParameterGroupification p) :=
  (qParameterCompatibleRoots p).root_one

noncomputable def qParameterKummerRealization :
    LocalMLFModelTMPair.IntegralKummerRootRealization p
      (LocalMLFModelTMPair.monoAnalytic p)
      ((LocalMLFModelTMPair.monoAnalytic p).openStabilizer p (qParameter p))
      (qParameter p) :=
  LocalMLFModelTMPair.canonicalIntegralKummerRootRealization
    p (LocalMLFModelTMPair.monoAnalytic p) (qParameter p)

theorem qParameterKummerRealization_root_one :
    (qParameterKummerRealization p).rootSystem.roots 1 =
      Additive.ofMul (qParameterGroupification p) :=
  (qParameterKummerRealization p).rootSystem.root_one

end LocalIntegralMonoid

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def concreteLocalQParameterRoots : Obligation :=
  { id := "IUT-II.concrete-local-q-parameter-roots"
    source := "IUT II, local q-parameter and Kummer root system"
    status := VerificationStatus.testCarrier
    note :=
      "The nontrivial local parameter p is placed in the actual nonzero " ++
        "integral-closure monoid and its Grothendieck groupification. The " ++
        "proved algebraic-closure divisibility construction gives a coherent " ++
        "rational-root system, and the groupification maps back to the same q. " ++
        "This remains a local carrier result; etale/Frobenioid identification " ++
        "and theta-link compatibility are not claimed."
    dependsOn :=
      [ "IUT-I-II.local-prime-place-carrier",
        "IUT-II.local-torsion-cyclotome" ] }

end LeanFormal.IUT.Audit
