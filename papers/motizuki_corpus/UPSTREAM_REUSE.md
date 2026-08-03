# Upstream Reuse Register

This register records source code that may be copied or ported into the
production tree. A copied declaration keeps its upstream commit, source-paper
location, Lean/Mathlib version, and local axiom status. A source interface or
opaque proposition is never promoted to a proved theorem merely because its
file compiles.

| repository and fixed reference | useful source surfaces | current decision |
|---|---|---|
| [promachina/iut-lean](https://github.com/promachina/iut-lean/commit/02ab3deda6b296f74257138c28ff25ecb51aac67), `02ab3de` checked 2026-08-03 | `EtaleThetaQuotient`, source initial-theta data, source Hodge theater, source prime strips, Kummer faithfulness, source Frobenioid birationalization, glued anabelioids, tempered covering/recovery, `SourceTheorem311`, Step-XI dependency audits | Preferred source-faithful upstream. Its 152-file tree is not imported wholesale: it pins Mathlib `v4.30.0`, while this project uses Lean/Mathlib `4.32.2`. The lower-central quotient kernel has been ported and audited in `IUTII/Theta/EtaleThetaQuotient.lean`. |
| [Takkun-kohinata/IUT_LEAN](https://github.com/Takkun-kohinata/IUT_LEAN/tree/9d56c46), `9d56c46` | `ThetaGroup`, `MonoTheta`, prime-strip and Frobenioid degree kernels, compatible roots, log-shell/log-Kummer, multiradial Ind1--Ind3 kernels, and explicit `IdentificationAudit`/`TranscriptionDegeneracy` diagnostics | Reuse proved elementary/group/order lemmas after declaration-level audit. The finite/model routes and hull diagnostics remain separate; they do not discharge the IUT-specific source bridge. |
| [lana-project/iut4-sec1](https://github.com/lana-project/iut4-sec1/tree/a7551d2), `a7551d2` | Mathlib-only IUT IV Section-1 numerical propositions and local-field exercises | Reuse only the elementary Section-1 kernels; no IUT I--III or Corollary 3.12 carrier is assumed. |
| [com-junkawasaki/iut-lean](https://github.com/com-junkawasaki/iut-lean/tree/ca4c0dd), `ca4c0dd` | Polynomial `abc`/Mason--Stothers and hyperbolic-curve numerical facts | Independent ABC-related mathematics, not an IUT route. Candidate standard number-theory lemmas only. |
| [PriestAmbrose/IUT-Corollary3_12-Lean](https://github.com/PriestAmbrose/IUT-Corollary3_12-Lean/tree/e5d5d20), `e5d5d20` | Small axioms-first Corollary 3.12 boundary vocabulary | Registry and comparison reference only; its abstract theorem is not evidence for the disputed implication. |

## Reuse status labels

- `proved`: Lean checks the declaration without `sorryAx`; it may be reused
  after adapting imports and namespaces.
- `interface`: a typed carrier or obligation is present, but the source
  construction is not proved; it must remain an explicit field in this tree.
- `diagnostic`: a theorem tests consistency, degeneracy, or a disputed
  transcription; it is not a proof of Corollary 3.12.
- `external-claim`: a paper or preprint claims a route; no result is imported
  as an axiom.

The current production trust boundary is checked independently by
`verification/axiom_audit.lean`, `tools/check_axiom_boundary_logged.ps1`, and
`tools/check_no_custom_axioms.ps1`.
