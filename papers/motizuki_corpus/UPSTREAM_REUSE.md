# Public Implementation Reuse Register

This register records earlier public implementations that may be copied or
ported into the production tree. "Upstream" is used only for a concrete Git
provenance relation. A copied declaration keeps its source commit,
source-paper location, Lean/Mathlib version, and local axiom status. A typed
interface or opaque proposition is never promoted to a proved theorem merely
because its file compiles.

| repository and fixed reference | useful source surfaces | current decision |
|---|---|---|
| [promachina/iut-lean](https://github.com/promachina/iut-lean/commit/c7c06e23d191037424ba5d1a336a31a8cf73dc78), production snapshot `0d52e0fd`, refreshed HEAD and all 25 non-master branches checked 2026-08-04 | 190 Lean files. The source-facing anabelioid, glued finite-etale, Galois-level, combinatorial universal-cover, tempered-cover, and Theorem-3.11 surfaces are the closest public implementation. Commit `04ffcc8e` adds real countable-base/finite-fiber and tempered-deck projection proofs; `ca36ee8d` adds finite semigraph and categorical comparison kernels; `c8c4a4b4` and `18e1ad97` add an Andre exact-sequence boundary and arithmetic tempered-tower wrapper; `198de794` assembles a selected finite-place covering boundary. All non-master tips are merged into `master` except one empty-tree commit. | Selective reuse only. The foundation closure, connected-cover/temperoid and quotient kernels, and the literal tempered-deck transition/projection chain are audited under Mathlib 4.32.2. Andre exactness/completion, stable-log specialization, level exactness, arithmetic limit surjectivity/inducing, and the selected bad-place stable/Andre/tower family remain record fields; their wrappers are not evidence for the source theorems. |
| [Takkun-kohinata/IUT_LEAN](https://github.com/Takkun-kohinata/IUT_LEAN/tree/9d56c46), `9d56c46`, refreshed 2026-08-04 with no newer default-branch commit | `ThetaGroup`, `MonoTheta`, prime-strip and Frobenioid degree kernels, compatible roots, log-shell/log-Kummer, multiradial Ind1--Ind3 kernels, and explicit `IdentificationAudit`/`TranscriptionDegeneracy` diagnostics | Reuse proved elementary/group/order lemmas after declaration-level audit. The finite/model routes and hull diagnostics remain separate; they do not discharge the IUT-specific source bridge. |
| [lana-project/iut4-sec1](https://github.com/lana-project/iut4-sec1/tree/a7551d2), `a7551d2`, refreshed 2026-08-04 with no newer default-branch commit | Mathlib-only IUT IV Section-1 numerical propositions and local-field exercises | Reuse only the elementary Section-1 kernels; no IUT I--III or Corollary 3.12 carrier is assumed. |
| [com-junkawasaki/iut-lean](https://github.com/com-junkawasaki/iut-lean/tree/ca4c0dd), `ca4c0dd`, refreshed 2026-08-04 with no newer default-branch commit | Polynomial `abc`/Mason--Stothers and hyperbolic-curve numerical facts | Independent ABC-related mathematics, not an IUT route. Candidate standard number-theory lemmas only. |
| [PriestAmbrose/IUT-Corollary3_12-Lean](https://github.com/PriestAmbrose/IUT-Corollary3_12-Lean/tree/e5d5d20), `e5d5d20`, refreshed 2026-08-04 with no newer default-branch commit | Small axioms-first Corollary 3.12 boundary vocabulary | Registry and comparison reference only; its abstract theorem is not evidence for the disputed implication. |

## Four-way reuse decision

- `direct-proof`: copy an exact construction or theorem after checking its
  statement against the paper and confirming that Lean reports no `sorryAx`.
- `migrated-proof`: preserve the mathematical statement and proof architecture
  while adapting only Lean/Mathlib interfaces; record the source diff.
- `interface-only`: use a typed record only to name an unresolved obligation.
  A theorem obtained by projecting such a field remains conditional.
- `excluded`: do not import packaging, regression-only aliases, duplicate
  enumeration, or modules unrelated to the current dependency path.

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
