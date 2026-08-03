/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.SourceTrace.IUTIVPaperLedger
import Iut.Stage1.IUTStage1IUTIVAlgebra
import Iut.Stage1.IUTStage1Theorem311
import Iut.Stage1.IUTStage1StepXI.Core

/-!
# IUT IV source-surface axiom audit

Representative endpoints from each implemented IUT IV clause remain visible to
Lean's axiom reporter.  The ledger classifies these endpoints as partial or
conditional even when their internal ordered-real proof is axiom-free.
-/

set_option linter.style.longLine false

#print axioms Iut.SourceTrace.iutIVSourceDocuments_exact
#print axioms Iut.SourceTrace.iutIVPaperLedger_ids_nodup
#print axioms Iut.SourceTrace.iutIVOwnedDeclarations_nodup
#print axioms Iut.Stage1.iutIVFiniteExtensionHaarCompactOpenLogVolumeEndpoint
#print axioms
  Iut.Stage1.IUTStage1IUTIVProposition14DistinguishedLocalLogShellConstructionSource.endpoint
#print axioms
  Iut.Stage1.IUTStage1IUTIVProposition14NondistinguishedLocalLogShellConstructionSource.endpoint
#print axioms
  Iut.Stage1.IUTStage1IUTIVProposition15ArchimedeanMetricConstructionSource.endpoint
#print axioms
  Iut.Stage1.IUTStage1IUTIVPrimeProductCaseSplitBoundShadow.primeProductLogTerm_le_uniform
#print axioms Iut.Stage1.IUTStage1IUTIVArithmeticDivisorSource.degree_eq_sum_localDegree
#print axioms Iut.Stage1.iutIVThetaPilotFinalCoefficientEstimate
#print axioms
  Iut.Stage1.IUTStage1IUTIVTheorem110PropositionLogShellFormulaSource.endpoint
#print axioms
  Iut.Stage1.IUTStage1IUTIVTheorem110FinalDisplayShadow.oneSixthLogQ_le_finalRightHandSide
#print axioms
  Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.IUTIVCThetaObligations.iutIVCThetaPlusOneEqArithmeticGapConstructed
#print axioms
  Iut.Stage1.IUTStage1Theorem311ToCorollary312PaperTrace.Obligations.IUTStage1IUTIVLocalArithmeticDegreeResidualSource.endpoint
#print axioms
  Iut.Stage1.IUTStage1IUTIVTheoremABoundedDiscrepancyShadow.theoremA_bounded_discrepancy_endpoint
#print axioms
  Iut.Stage1.IUTStage1IUTIVCorollary22BoundedDiscrepancyChainShadow.bounded_discrepancy_chain_endpoint
#print axioms
  Iut.Stage1.IUTStage1IUTIVCorollary22FinalHBoundShadow.final_h_bound_endpoint
#print axioms
  Iut.Stage1.IUTStage1IUTIVCorollary22FiniteExceptionTheoremAShadow.finite_exception_theoremA_endpoint
#print axioms
  Iut.Stage1.IUTStage1IUTIVCorollary23DiophantineInequalityShadow.diophantine_inequality_endpoint
