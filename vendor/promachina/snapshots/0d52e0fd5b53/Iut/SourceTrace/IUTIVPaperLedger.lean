/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.SourceTrace.M1M3PaperLedger

/-!
# IUT IV primary-source ledger

This downstream ledger extends the stable IUT I--III audit with the IUT IV
surface currently exposed by Stage 1.  It deliberately distinguishes exact
ordered-real algebra from supplied source hypotheses and from geometric
constructions that have not been formalized.

Page references are printed page numbers in the repository's exact copy of
IUT IV.  `partialImplementation` never means that the paper theorem has been
proved: in this file it includes conditional records and explicitly named
`Shadow` declarations whose source inputs remain open.
-/

namespace Iut.SourceTrace

/-- Exact local copy of the IUT IV paper used for this audit. -/
def iutIVSourceDocuments : List PaperSourceDocument :=
  [ { volume := .iutIV,
      repositoryPath := "docs/papers/mochizuki-iut-iv.pdf",
      sha256 := "5bf4b1e0a8c2686562a6859e5009d301335044cfb5efec5d3a9edf764e4af87f" } ]

/-- The IUT IV manifest contains exactly the hash-pinned paper artifact. -/
theorem iutIVSourceDocuments_exact :
    iutIVSourceDocuments =
      [ { volume := .iutIV,
          repositoryPath := "docs/papers/mochizuki-iut-iv.pdf",
          sha256 :=
            "5bf4b1e0a8c2686562a6859e5009d301335044cfb5efec5d3a9edf764e4af87f" } ] :=
  rfl

private def iutIVClause
    (id source : String) (leanDeclarations : List String)
    (status : ClauseStatus) (gap : String) : PaperClause :=
  { id, volume := .iutIV, source, leanDeclarations, status, gap }

/-!
The entries below own the public, source-facing declaration families rather
than claiming that every generated projection is a distinct implementation.
Splits follow genuine changes of status: exact elementary algebra, conditional
local estimates, missing hypotheses, and downstream integration are kept
separate.
-/

/-- Clause-level source ownership for the public IUT IV Lean surface. -/
def iutIVPaperLedger : List PaperClause :=
  [ iutIVClause "IV.A" "IUT IV, Theorem A, p. 3"
      ["Iut.Stage1.IUTStage1IUTIVTheoremABoundedDiscrepancyShadow",
        "Iut.Stage1.IUTStage1IUTIVTheoremABoundedDiscrepancyShadow.theoremA_bounded_discrepancy_endpoint"]
      .partialImplementation
      "The bounded-discrepancy conclusion is stored as a hypothesis over an arbitrary point type. The degree-bounded algebraic-point domain and the Diophantine construction remain open in #72; this shadow is not a proof of Theorem A.",
    iutIVClause "IV.1.4(i-ii)" "IUT IV, Proposition 1.4(i)-(ii), pp. 13-14"
      ["Iut.Stage1.IUTStage1IUTIVFiniteExtensionHaarCompactOpenLogVolumeEndpoint",
        "Iut.Stage1.iutIVFiniteExtensionHaarCompactOpenLogVolumeEndpoint",
        "Iut.Stage1.IUTStage1IUTIVCompactOpenTopologyHaarNormalizationEndpoint",
        "Iut.Stage1.iutIVCompactOpenTopologyHaarNormalizationEndpoint",
        "Iut.Stage1.IUTStage1IUTIVAdditiveHaarCompactOpenNormalizationEndpoint",
        "Iut.Stage1.iutIVAdditiveHaarCompactOpenNormalizationEndpoint"]
      .partialImplementation
      "The finite-extension, compact-open, and additive-Haar normalization laws are typed endpoints, but their local-field and measure-theoretic source objects are supplied rather than constructed from Proposition 1.4.",
    iutIVClause "IV.1.4(iii)" "IUT IV, Proposition 1.4(iii), pp. 13-14"
      ["Iut.Stage1.IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate",
        "Iut.Stage1.IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate.endpoint",
        "Iut.Stage1.IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource",
        "Iut.Stage1.IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource.endpoint",
        "Iut.Stage1.IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource",
        "Iut.Stage1.IUTStage1IUTIVProposition14DistinguishedAdditiveHaarLogShellSource.endpoint"]
      .partialImplementation
      "The distinguished log-shell inclusions and numerical bounds are explicit conditional source records. Constructing their valuation, theta-value, and log-shell inputs from the paper remains open in #70.",
    iutIVClause "IV.1.4(iv)" "IUT IV, Proposition 1.4(iv), p. 14"
      ["Iut.Stage1.IUTStage1IUTIVProposition14NondistinguishedLocalLogShellEstimate",
        "Iut.Stage1.IUTStage1IUTIVProposition14NondistinguishedLocalLogShellEstimate.endpoint",
        "Iut.Stage1.IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource",
        "Iut.Stage1.IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource.endpoint",
        "Iut.Stage1.IUTStage1IUTIVProposition14NondistinguishedAdditiveHaarLogShellSource",
        "Iut.Stage1.IUTStage1IUTIVProposition14NondistinguishedAdditiveHaarLogShellSource.endpoint"]
      .partialImplementation
      "The nondistinguished zero-contribution calculation is derived once the local construction record is supplied. The paper's actual local objects and inclusions are not yet constructed.",
    iutIVClause "IV.1.5(i-iv)" "IUT IV, Proposition 1.5(i)-(iv), pp. 14-16"
      ["Iut.Stage1.iutIVProp15ArchimedeanDirectSummandCount",
        "Iut.Stage1.IUTStage1IUTIVProposition15ArchimedeanLocalMetricEstimate",
        "Iut.Stage1.IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource",
        "Iut.Stage1.IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource.endpoint"]
      .partialImplementation
      "The direct-summand count and ordered-real metric bound are explicit. The tensor-product metric, invariant integral structure, and containment are fields of the source record, not constructions from Proposition 1.5.",
    iutIVClause "IV.1.6" "IUT IV, Proposition 1.6, p. 16"
      ["Iut.Stage1.IUTStage1IUTIVPrimeProductCaseSplitBoundShadow",
        "Iut.Stage1.IUTStage1IUTIVPrimeProductCaseSplitBoundShadow.primeProductLogTerm_le_uniform"]
      .partialImplementation
      "Lean proves the final real-valued case split from two supplied case bounds. It does not construct the prime-product estimate or its arithmetic hypotheses.",
    iutIVClause "IV.1.7" "IUT IV, Proposition 1.7, pp. 16-17"
      ["Iut.Stage1.IUTStage1IUTIVProposition14DistinguishedLocalLogShellEstimate.proposition17_weighted_average_le_exact_procession",
        "Iut.Stage1.IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource.proposition17_weighted_average_le_exact_procession"]
      .partialImplementation
      "The weighted-average comparison is exposed as a required projection in the distinguished local source. Lean composes it into the Step (v) bound but does not derive Proposition 1.7.",
    iutIVClause "IV.1.8(i-vii)" "IUT IV, Proposition 1.8(i)-(vii), pp. 18-21"
      [] .unformalized
      "No public declaration constructs the proposition's elliptic-torsion fields, ramification, differents, conductors, or degree estimates. Nearby tripodal real-number shadows do not implement Proposition 1.8.",
    iutIVClause "IV.1.9(i-ii)" "IUT IV, Definition 1.9(i)-(ii), pp. 21-22"
      ["Iut.Stage1.IUTStage1IUTIVArithmeticDivisorSource",
        "Iut.Stage1.IUTStage1IUTIVArithmeticDivisorSource.degree_eq_sum_localDegree",
        "Iut.Stage1.IUTStage1IUTIVTheorem110ArithmeticDivisorSource",
        "Iut.Stage1.IUTStage1IUTIVTheorem110ArithmeticDivisorSource.endpoint"]
      .partialImplementation
      "Finite arithmetic divisors, support, effectiveness, and degree sums are typed. The particular different, conductor, q-parameter, and theta divisors required by the paper remain supplied source data.",
    iutIVClause "IV.1.10.hypotheses" "IUT IV, Theorem 1.10 hypotheses, pp. 22-23"
      [] .unformalized
      "The source hypotheses on the initial theta data, field tower, ramification, q-parameters, and arithmetic divisors are not constructed. This is the explicit blocker tracked by #70.",
    iutIVClause "IV.1.10(i-iv,viii)" "IUT IV, Theorem 1.10 Steps (i)-(iv),(viii), pp. 23-29"
      ["Iut.Stage1.iutIVThetaPilotArithmeticUpperTerm",
        "Iut.Stage1.iutIVThetaPilotMainLogTerm",
        "Iut.Stage1.iutIVThetaPilotFinalCoefficientEstimate",
        "Iut.Stage1.iutIVThetaPilot_average_sum_id",
        "Iut.Stage1.iutIVThetaPilot_average_sum_sq",
        "Iut.Stage1.iutIVSmallPrimeGLTwoDegreeExpression_eq",
        "Iut.Stage1.IUTStage1IUTIVFinalErrorAbsorptionShadow.finalError_le_ten"]
      .partialImplementation
      "The elementary identities and corrected coefficients 12 and 20 are proved (#69). Arithmetic quantities entering the estimates remain parameters or supplied bounds, so these exact calculations do not prove Theorem 1.10.",
    iutIVClause "IV.1.10(v-vii)" "IUT IV, Theorem 1.10 Steps (v)-(vii), pp. 25-27"
      ["Iut.Stage1.IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource",
        "Iut.Stage1.IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource.endpoint",
        "Iut.Stage1.IUTStage1IUTIVTheorem110LocalAnalyticConstructionFormulaSource",
        "Iut.Stage1.IUTStage1IUTIVTheorem110LocalAnalyticConstructionFormulaSource.endpoint",
        "Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.IUTIVLocalAnalyticCThetaSourceData"]
      .partialImplementation
      "The three local cases are assembled and checked from Proposition 1.4/1.5-shaped records. The records still assume the decisive inclusions, local formula bounds, and metric containment; see #70.",
    iutIVClause "IV.1.10(final)" "IUT IV, Theorem 1.10 final estimate, pp. 29-31"
      ["Iut.Stage1.IUTStage1IUTIVThetaPilotLogVolumeEstimateShadow",
        "Iut.Stage1.IUTStage1IUTIVTheorem110FinalDisplayShadow",
        "Iut.Stage1.IUTStage1IUTIVTheorem110FinalDisplayShadow.oneSixthLogQ_le_finalRightHandSide",
        "Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.IUTIVTheorem110CThetaSourceData",
        "Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.IUTIVCThetaSourceData",
        "Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.IUTIVCThetaObligations.iutIVCThetaPlusOneEqArithmeticGapConstructed"]
      .partialImplementation
      "Lean verifies the final ordered-real chain from the C_Theta identity, lower bound, local estimates, and base-change comparison. Those source inputs are supplied; the declaration is intentionally a shadow, not source-faithful.",
    iutIVClause "IV.1.10(xi)-III.3.12" "IUT IV, Theorem 1.10 Step (xi) handoff, pp. 27-29"
      ["Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource",
        "Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource.endpoint",
        "Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallCaseBoundedPointwiseResidualSource",
        "Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVTheorem110ValuationBallCaseBoundedPointwiseResidualSource.endpoint"]
      .partialImplementation
      "The bounded local consumer and residual identities are formal once their source records are supplied. Constructing the IUT III Corollary 3.12 to IUT IV Theorem 1.10 arithmetic handoff remains the downstream integration boundary #26.",
    iutIVClause "IV.2.1(i-ii)" "IUT IV, Proposition 2.1(i)-(ii), pp. 40-41"
      [] .unformalized
      "The global height, different, conductor, and q-height comparison for bounded-degree points has no source construction in Lean. Corollary 2.2 shadows accept the resulting functions and bounds as data.",
    iutIVClause "IV.2.2(i)" "IUT IV, Corollary 2.2(i), pp. 41-42"
      ["Iut.Stage1.IUTStage1IUTIVCorollary22BoundedDiscrepancyChainShadow",
        "Iut.Stage1.IUTStage1IUTIVCorollary22BoundedDiscrepancyChainShadow.bounded_discrepancy_chain_endpoint"]
      .partialImplementation
      "Lean composes three supplied bounded-discrepancy equivalences. It does not construct the height functions or prove the three source comparisons; see #71.",
    iutIVClause "IV.2.2(ii)" "IUT IV, Corollary 2.2(ii), pp. 42-48"
      ["Iut.Stage1.IUTStage1IUTIVCorollary22C1PrimeScaleWindowShadow",
        "Iut.Stage1.IUTStage1IUTIVCorollary22Theorem110ToC2FirstBoundShadow",
        "Iut.Stage1.IUTStage1IUTIVCorollary22C2InequalityChainShadow",
        "Iut.Stage1.IUTStage1IUTIVCorollary22FinalHBoundShadow",
        "Iut.Stage1.IUTStage1IUTIVCorollary22FinalHBoundShadow.final_h_bound_endpoint",
        "Iut.Stage1.IUTStage1IUTIVCorollary22ToTheoremABoundShadow.theoremA_handoff_endpoint"]
      .partialImplementation
      "The C1/C2 and epsilon manipulations are proved as conditional real algebra. Prime selection, height comparison, and the geometric exceptional-set construction are not supplied by the source; see #71 and #72.",
    iutIVClause "IV.2.2(iii)" "IUT IV, Corollary 2.2(iii), pp. 48-50"
      ["Iut.Stage1.IUTStage1IUTIVCorollary22FiniteExceptionTheoremAShadow",
        "Iut.Stage1.IUTStage1IUTIVCorollary22FiniteExceptionTheoremAShadow.finite_exception_theoremA_endpoint"]
      .partialImplementation
      "Finite-exception lower bounds are glued after both generic and exceptional bounds are supplied. The source's finite exceptional set and its arithmetic bounds are not constructed; see #71 and #72.",
    iutIVClause "IV.2.3" "IUT IV, Corollary 2.3, pp. 54-55"
      ["Iut.Stage1.IUTStage1IUTIVCorollary23DiophantineInequalityShadow",
        "Iut.Stage1.IUTStage1IUTIVCorollary23DiophantineInequalityShadow.diophantine_inequality_endpoint"]
      .partialImplementation
      "The GenEll transfer is an explicit hypothesis, and the point type is not the paper's degree-bounded algebraic-point domain. The Diophantine conclusion therefore remains a conditional shadow tracked by #72." ]

/-- Clause identifiers at a selected IUT IV audit status. -/
def iutIVClauseIdsWithStatus (status : ClauseStatus) : List String :=
  iutIVPaperLedger.filterMap fun entry =>
    if entry.status = status then some entry.id else none

/-- All declaration names assigned an IUT IV clause owner. -/
def iutIVOwnedDeclarations : List String :=
  iutIVPaperLedger.flatMap PaperClause.leanDeclarations

/-- Implementation claims must name at least one public Lean declaration. -/
def iutIVImplementationClaimsHaveDeclarations : Bool :=
  iutIVPaperLedger.all fun entry =>
    entry.status = .unformalized || !entry.leanDeclarations.isEmpty

/-- The older ledger retains its independently checked 131 entries. -/
theorem m1m3PaperLedger_stable_count : m1m3PaperLedger.length = 131 :=
  m1m3PaperLedger_count

/-- The IUT IV audit has nineteen status-separated clause entries. -/
theorem iutIVPaperLedger_count : iutIVPaperLedger.length = 19 :=
  rfl

/-- No IUT IV source clause occurs twice. -/
theorem iutIVPaperLedger_ids_nodup :
    (iutIVPaperLedger.map PaperClause.id).Nodup := by
  decide

/-- Every registered public declaration has exactly one clause owner. -/
theorem iutIVOwnedDeclarations_nodup : iutIVOwnedDeclarations.Nodup := by
  set_option maxRecDepth 4096 in
    decide

/-- Every partial implementation names its owned public Lean surface. -/
theorem iutIVImplementationClaimsHaveDeclarations_eq_true :
    iutIVImplementationClaimsHaveDeclarations = true :=
  rfl

/-- Sixteen clauses have genuine but incomplete or conditional Lean content. -/
theorem iutIVPartialImplementation_count :
    (iutIVClauseIdsWithStatus .partialImplementation).length = 16 :=
  rfl

/-- Three named IUT IV source clauses have no implementation. -/
theorem iutIVUnformalized_count :
    (iutIVClauseIdsWithStatus .unformalized).length = 3 :=
  rfl

/-- The IUT IV ledger contains no toy-model claim. -/
theorem iutIVToyModel_count :
    (iutIVClauseIdsWithStatus .toyModel).length = 0 :=
  rfl

/-- No IUT IV theorem or corollary is currently claimed source-faithful. -/
theorem iutIVSourceFaithful_count :
    (iutIVClauseIdsWithStatus .sourceFaithful).length = 0 :=
  rfl

end Iut.SourceTrace
