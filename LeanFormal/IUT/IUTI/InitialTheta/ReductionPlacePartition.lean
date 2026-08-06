import LeanFormal.IUT.Foundations.Geometry.LocalReduction
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve

/-!
  Set-theoretic place carriers for the initial-theta reduction split.

  The definitions retain the actual finite places and the actual curve-level
  reduction predicates.  The lemmas give the stable-reduction inclusions and
  the exact union identity.  They do not assert that a chosen curve has a
  nonempty multiplicative locus.
-/

namespace LeanFormal.IUT

namespace PuncturedEllipticCurve

variable {F : Type*} [Field F] [NumberField F]

def goodReductionPlaces (X : PuncturedEllipticCurve F) :
    Set (NumberField.FinitePlace F) :=
  {place | X.HasGoodReductionAt place}

def multiplicativeReductionPlaces (X : PuncturedEllipticCurve F) :
    Set (NumberField.FinitePlace F) :=
  {place | X.HasMultiplicativeReductionAt place}

def stableReductionPlaces (X : PuncturedEllipticCurve F) :
    Set (NumberField.FinitePlace F) :=
  {place | X.HasStableReductionAt place}

theorem stableReductionPlaces_eq_union (X : PuncturedEllipticCurve F) :
    X.stableReductionPlaces =
      X.goodReductionPlaces ∪ X.multiplicativeReductionPlaces :=
  rfl

theorem goodReductionPlaces_subset_stable (X : PuncturedEllipticCurve F) :
    X.goodReductionPlaces ⊆ X.stableReductionPlaces := by
  intro place hplace
  exact X.hasGoodReductionAt_imp_stable hplace

theorem multiplicativeReductionPlaces_subset_stable
    (X : PuncturedEllipticCurve F) :
    X.multiplicativeReductionPlaces ⊆ X.stableReductionPlaces := by
  intro place hplace
  exact X.hasMultiplicativeReductionAt_imp_stable hplace

theorem stableReductionPlaces_iff (X : PuncturedEllipticCurve F)
    (place : NumberField.FinitePlace F) :
    place ∈ X.stableReductionPlaces ↔
      place ∈ X.goodReductionPlaces ∨
        place ∈ X.multiplicativeReductionPlaces :=
  Iff.rfl

end PuncturedEllipticCurve

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def initialThetaReductionPlacePartition : Obligation :=
  { id := "IUT-I.initial-theta-reduction-place-partition"
    source := "IUT I, Definition 3.1(b); stable/good/multiplicative places"
    status := VerificationStatus.proved
    note :=
      "Actual finite-place sets for good, multiplicative, and stable " ++
        "reduction are defined from the curve-level predicates. Stable is " ++
        "proved to be exactly the union of the two loci, with each locus " ++
        "included in it. Nonemptiness and the source's selected bad-place " ++
        "hypothesis remain separate."
    dependsOn := ["Foundations.Geometry.elliptic-local-reduction"] }

end LeanFormal.IUT.Audit
