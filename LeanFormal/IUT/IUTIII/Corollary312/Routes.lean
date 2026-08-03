/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-!
  Parallel proof routes for the Theorem 3.11 -> Corollary 3.12 wall.

  The first route is the RIMS/Mochizuki reorganization usually called
  "Theorem 3.11.5": the 2026 preliminary formalization report explains that
  this is shorthand for moving the `(hull+det)` part of Remark 3.9.5 into an
  intermediate checkpoint.  It is not a theorem numbered 3.11.5 in the
  published IUT I--IV papers.

  The second route records Kirti Joshi's Arithmetic Teichmuller Spaces III
  / Rosetta-Stone approach, which claims an independent proof of Corollary
  3.12 by constructing the relevant arithmetic Teichmuller spaces and the
  gluing data.  The two routes are kept separate: a certificate for one route
  is not silently reused as a proof for the other.

  A third, explicitly claimed route is recorded for Mikael Sarkisyan's
  Erdos--Kac based argument.  Its preprint calls itself another proof of
  Corollary 3.12, but this project treats that as a citable research claim
  only: no theorem, axiom, or certificate is imported from the preprint.

  This file contains only the typed route boundary and audit obligations.  It
  does not assert existence of either certificate.
-/

namespace LeanFormal.IUT

inductive Cor312Route
  | mochizuki3115
  | arithmeticTeichmuller
  | sarkisyanErdosKac
  deriving DecidableEq, Repr

structure Cor312RouteCertificate where
  route : Cor312Route
  contract : StepXIContract

theorem Cor312RouteCertificate.conclusion
    (certificate : Cor312RouteCertificate) :
    Cor312Conclusion certificate.contract := by
  exact cor312_of_constructed_stepXI certificate.contract

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def mochizuki3115Construction : Obligation :=
  { id := "IUT-III.theorem-3.11.5"
    source :=
      "Mochizuki, On the Formalization of IUT: a preliminary progress report, " ++
        "§4; IUT III, Remark 3.9.5"
    status := VerificationStatus.pending
    note :=
      "This is a source-labelled reorganization, not an original theorem " ++
        "number: move hull+det/descent into an intermediate checkpoint and " ++
        "prove Theorem 3.11 -> 3.11.5 using APT and IPL. The actual source " ++
        "construction and comparison invariants are not yet formalized."
    dependsOn :=
      [ "IUT-III.theorem-3.11-output",
        "IUT-III.Ind1",
        "IUT-III.Ind2",
        "IUT-III.Ind3",
        "IUT-III.APT",
        "IUT-III.IPL",
        "IUT-III.holomorphic-hull-determinant-log-volume" ] }

def mochizuki3115ToCor312 : Obligation :=
  { id := "IUT-III.theorem-3.11.5-to-corollary-3.12"
    source :=
      "Mochizuki, On the Formalization of IUT: a preliminary progress report, §4"
    status := VerificationStatus.pending
    note :=
      "Verify the fourth comparison square: SHE+IPL and the hull+det descent " ++
        "must produce one common-container comparison of q- and Theta-packets. " ++
        "No numerical inequality is assumed in this placeholder."
    dependsOn := [ "IUT-III.theorem-3.11.5", "IUT-III.SHE", "IUT-III.IPL" ] }

def arithmeticTeichmullerRoute : Obligation :=
  { id := "IUT-III.arithmetic-teichmuller-corollary-3.12-route"
    source :=
      "Kirti Joshi, Construction of Arithmetic Teichmuller Spaces III: " ++
        "A Rosetta Stone and a proof of Mochizuki's Corollary 3.12, arXiv:2401.13508"
    status := VerificationStatus.pending
    note :=
      "Formalize the alternative route through arithmetic Teichmuller spaces, " ++
        "the Rosetta-Stone correspondence, and the induced gluing of " ++
        "Hodge-theater/Frobenioid data. The cited paper's claimed proof is " ++
        "recorded as a research route, not imported as an axiom or treated as " ++
        "an established Lean theorem."
    dependsOn :=
      [ "IUT-I.initial-theta-arithmetic-data",
        "IUT-I.hodge-theater-carrier-and-links",
        "IUT-II.vertical-log-kummer",
        "IUT-III.theorem-3.11.5-to-corollary-3.12" ] }

def sarkisyanErdosKacRoute : Obligation :=
  { id := "IUT-III.sarkisyan-erdos-kac-route"
    source :=
      "Mikael Sarkisyan, Something about Inter-universal Teichmuller " ++
        "Theory, arXiv:2306.02448"
    status := VerificationStatus.pending
    note :=
      "The preprint explicitly claims another proof of Corollary 3.12 " ++
        "using an Erdos--Kac argument. This is a third claimed route, not " ++
        "an independently accepted proof: formalize its translation of " ++
        "IUT data and the probabilistic-to-deterministic bridge before any " ++
        "conclusion is trusted. No result from the preprint is imported as " ++
        "an axiom."
    dependsOn :=
      [ "IUT-I.initial-theta-arithmetic-data",
        "IUT-II.finite-theta-packet",
        "IUT-III.theorem-3.11-output" ] }

def routeComparisonAudit : Obligation :=
  { id := "IUT-III.route-comparison-audit"
    source :=
      "Mochizuki RIMS formalization report §4; Joshi arXiv:2401.13508; " ++
        "Sarkisyan arXiv:2306.02448"
    status := VerificationStatus.pending
    note :=
      "Keep the Mochizuki 3.11.5 route and the arithmetic-Teichmuller route " ++
        "as separate certificates, compare their assumptions and outputs, and " ++
        "accept a Corollary 3.12 conclusion only after one route has a complete " ++
        "zero-sorry construction."
    dependsOn :=
      [ "IUT-III.theorem-3.11.5-to-corollary-3.12",
        "IUT-III.arithmetic-teichmuller-corollary-3.12-route",
        "IUT-III.sarkisyan-erdos-kac-route" ] }

end LeanFormal.IUT.Audit
