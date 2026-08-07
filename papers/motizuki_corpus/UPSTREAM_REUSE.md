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

## Latest snapshot review (2026-08-06)

The refreshed `promachina/iut-lean` snapshot at
`1fa6387f11fb6dc67eb618b8138e6bc64f56b039` was built independently before
selective reuse.  Its `SourceIUTIIIRemark395WeightedDeterminant.lean` contains
the same denominator-product arithmetic used locally, but also couples it to
source-facing holomorphic-hull, realified-line, and realization records.  The
local production module `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/WeightedNormalization.lean`
therefore keeps only the proved arithmetic kernel and records the geometric
dependencies separately.  The upstream file is a reference for statement
alignment, not a bulk import.  The same decision applies to
`SourceKummerGaussianSynchronization.lean`: its elementary root/profile
lemmas are already covered by the local Kummer kernels, while its remaining
construction fields are not silently promoted to theorems.

The remote `origin/master` was refreshed at `9fd3d576` on 2026-08-06.  Its
newest C-to-D/E surfaces are useful for statement alignment, but they do not
show that C is complete.  `SourceBadLocalStableReduction.lean` genuinely proves
the finite one-component/one-node dual semi-graph facts (connectedness,
finiteness, closed node, and marked open edge); its tame cover categories and
pointed pullback are still fields of `SourceTateNodalTameRealization`.
`SourceIUTIIITheorem311.lean` proves transport and invariance lemmas only after
the source evaluation, procession, local tensor, upper-semi, and log-volume
data are supplied.  `SourceIUTIIICorollary312IPLSHE.lean` requires an
`SourceCorollary312AnalyticStepXIInput` carrying the Theorem 3.11 evaluation,
Remark 3.9.5 construction, determinant-line realization, admissible regions,
block log-volume equalities, and a vertical hull region.  The APT descent file
likewise retains the complete hidden source input before projecting a visible
output.  These are typed conditional constructions, not proofs of those
source objects' existence.  They are therefore `interface-only` except for
the small combinatorial graph lemmas; no bulk import is justified.  The remote
  repository is Apache-2.0, so any future copied code must retain its copyright,
  license, attribution, and a local modification record.

## Latest HEAD check (2026-08-07)

The public repository HEAD was checked read-only with `git ls-remote` and is
`e2da14360c854e3ac1ad946339d581f737766a34` (Apache-2.0). The transient review
checkout is not part of the production tree; the retained provenance is the
Apache-2.0 review record and the audited snapshots under
`vendor/promachina/snapshots/`.
The newest files add `SourceIUTIIIStepXIPacketCarrier`,
`SourceIUTIIIStepXIHullDeterminantBound`, measured-hull/preimage records, and
source-trace updates. Their useful results are projection, compactness, and
weighted determinant lemmas conditional on a supplied source evaluation and
packet decomposition. The existence of the source packet, its recognition
maps, and the source-faithful Step-XI input remain structure fields; no new
unconditional C-layer or Corollary-3.12 proof was found.

Decision for this tree: `interface-only` for those new files. The current
finite-label batch instead uses the already proved local packet and quotient
kernels, and its exact reuse is recorded in `AUDIT_LEDGER.md` and
`IUT_SUBTARGETS.md`. No upstream wrapper or unverified theorem was imported.
