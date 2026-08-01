# IUT audit ledger

This file records what was actually checked in this workspace. It is a scope
ledger, not a claim that IUT has been proved or refuted. Statuses mean:

- **proved**: Lean checked the statement without an IUT-specific premise being
  hidden in the proof;
- **interface**: Lean checked a theorem after a record/certificate containing
  the mathematical content was supplied;
- **claim only**: the code states the intended theorem or vocabulary, but does
  not prove its IUT-specific existence/construction;
- **not checked**: no local verification yet.

## Source snapshot

The source page was saved as `tmp/motizuki-papers-japanese.html` on 2026-08-02.
The selected original papers were downloaded from that page into
`tmp/motizuki/`; SHA-256 hashes are kept here so that later re-checks use the
same documents:

| source | SHA-256 (prefix) |
|---|---|
| IUT I | `7360E3ED27C235B5...` |
| IUT II | `180BFA6AADDC4AE3...` |
| IUT III | `9A7EE3C77B1C7717...` |
| IUT IV | `5BF4B1E0A8C26865...` |
| Panoramic Overview | `EB42575F73D69D1F...` |
| Essential Logical Structure | `C0E63B629AA174AA...` |
| Explicit estimates | `4CACCE3F1085C4F5...` |

The relevant text was extracted with `pypdf` (the PDF skill workflow) into
`tmp/motizuki/iut-iii-full.txt`, `tmp/motizuki/iut-iii-proof-3-12.txt`, and
`tmp/motizuki/iut-iv-intro.txt`. The page numbers below are PDF page numbers
and also show the printed page in the extracted text.

## What the original papers require

1. **IUT I-II (prerequisites):** initial Theta data, distinct Hodge-theater
   histories, prime strips, Hodge-Arakelov theta evaluation, Gaussian/LGP
   monoids, and the Kummer/coric infrastructure. No local Lean project here
   constructs these objects from an elliptic curve and its number field.
2. **IUT III, Theorem 3.11:** a multiradial output consisting of tensor packets
   of log-shells, splitting monoids, and labelled copies of `F_mod`, with
   `(Ind1)`, `(Ind2)`, `(Ind3)` and the stated Kummer/link compatibilities.
3. **IUT III, Corollary 3.12:** the disputed final passage is explicit in the
   proof, especially PDF pages 174--184 (printed pp. 174--184):
   `IPL` links the output to the q-pilot prime strip; `SHE` says the output is
   expressible in the fixed 1-column arithmetic holomorphic structure;
   `APT` justifies the algorithmic transport; the holomorphic hull and
   log-volume then yield `-|log(q)| in R_{<= -|log(Theta)|}`. This is the
   logical wall. It is not just a numerical `j^2` calculation.
4. **IUT IV:** its abstract theorem (PDF pp. 1--3) and the Section 1/2
   estimates use IUT III Corollary 3.12 (e.g. the explicit final step on PDF
   p. 31 and the discussion beginning p. 40). Thus an IUT IV numerical proof
   cannot close the earlier wall by itself.

The LANA interim report (`papers/LANA_report_202607.pdf`, extracted in
`tmp/pdfs/lana.txt`) independently describes the same remaining obligation:
the q-pilot-native construction must be compatible with the multiradial/
Kummer construction after Ind1--3; its abstract (PDF p. 1) says the proof has
not been reconstructed, and pp. 4--6 call this diagram-commutativity/
identity issue the ``wall``. This is a status report, not a verdict.

## Local Lean checks

### Minimal diagnostic model (this workspace)

| file | status | checked fact | limitation |
|---|---|---|---|
| `LeanFormal/IUTDispute.lean` | **proved** | In a same ordered space, monotonicity makes the comparison tautological; with `q < 0`, `factor > 1`, `theta = factor*q`, a tight-hull premise `q <= hull <= theta` is inconsistent; a slack witness satisfies the receiver/common-container shape while violating tightness. | This is an order-theoretic diagnostic. It does not define Hodge theaters, Kummer maps, or the source of the premises. |
| `LeanFormal/Basic.lean` | **proved** (separate analysis exercise) | A real-analysis limit problem is fully checked and is unrelated to IUT. | It must not be counted as IUT progress. |

The diagnostic therefore supports only: **the dispute is a missing/contested
identification or compatibility premise, not an arithmetic contradiction in the
abstract inequality.** It does not decide which side is mathematically right.

### Public repositories checked at fixed commits

| repository (commit) | build/scope actually observed | status at the IUT wall |
|---|---|---|
| [promachina/iut-lean](https://github.com/promachina/iut-lean) `4953e647` | 128 Lean files. The project has an extensive Stage-1 source-facing layer and its own dependency/audit documents. `AlgorithmicOutput` stores `ipl`, `she`, `apt` as `Prop` fields; downstream `CorollarySchema`/`SourceObligations` prove the ordered comparison once certificates, a common-target bound, hull/measure data, and q-positivity are supplied. | **interface**. The repository README explicitly lists full Frobenioids, holomorphic hulls, determinants, and local-field/Haar compatibility as remaining construction work. A passing downstream theorem is conditional on those records. |
| [Takkun-kohinata/IUT_LEAN](https://github.com/Takkun-kohinata/IUT_LEAN) `9d56c46` | 68 Lean files. `Multiradial/Cor312.lean` proves its stated abstract corridor; `Diophantine/Szpiro.lean` defines the Szpiro-shaped conclusion but leaves its truth as `DiophantineMainTheorem`; `InitialThetaData/Deferred.lean` documents deferred geometric realization; `LogTheta/Indeterminacy.lean` uses an orbit model for Ind3. | **interface/claim only**. The finite/group-theoretic and numerical lemmas are useful, but the real etale-theta, prime-strip, Kummer, and initial-data constructions are not recovered from the original geometry. |
| [lana-project/iut4-sec1](https://github.com/lana-project/iut4-sec1) `a7551d2` | 26 Lean files. Six Mathlib-only Section-1 targets are exported. The comparator README marks later targets (tensor bijection/norm, second error, exact prime-counting) as not included or conditional. | **proved only for elementary Section 1 fragments**. It intentionally does not verify IUT I--III or Corollary 3.12. |
| [com-junkawasaki/iut-lean](https://github.com/com-junkawasaki/iut-lean) `ca4c0dd` | 7 Lean files. Genuine `Polynomial.abc`/Mason--Stothers corollary and numerical hyperbolic curve-type facts. | **not IUT formalization**; no prime strips or Corollary 3.12 objects. |
| [PriestAmbrose/IUT-Corollary3_12-Lean](https://github.com/PriestAmbrose/IUT-Corollary3_12-Lean) `e5d5d20` | 5 Lean files. Axioms-first skeleton; `Cor312.lean` has the abstract theorem with `sorry`. | **claim only**; useful as a dependency ledger, not evidence for the disputed implication. |

These repositories are complementary rather than independent completed proofs:
the closest source-facing implementation is promachina's, the most explicit
axioms/deferral ledger is Takkun's, iut4-sec1 covers elementary downstream
arithmetic, and the other two are scaffolds or unrelated proven mathematics.

## Outstanding obligations (the checklist to update)

The following must become concrete Lean definitions and proofs before anyone
can claim that the wall has been crossed:

- Construct the actual IUT I initial Theta data and distinct Hodge-theater
  histories from the stated number field/elliptic-curve hypotheses.
- Construct the IUT I-II prime strips, Hodge-Arakelov evaluation, theta/LGP
  monoids, mono-theta cyclotomic rigidity, and the vertical log-Kummer
  correspondence; do not replace them by an arbitrary record with the same
  field names.
- Construct Theorem 3.11's multiradial algorithm and prove its Ind1/Ind2
  quotient and Ind3 upper-semi compatibility from that construction.
- Prove the horizontal/vertical compatibility needed to transport the output
  into the 1-column while preserving the q-pilot's fixed arithmetic-holomorphic
  condition (the paper's `SHE` and `APT`).
- Define the holomorphic hull, determinant/tensor normalization, and local/global
  log-volume maps and prove the comparison that gives membership in
  `R_{<= -|log(Theta)|}`.
- Only after those items, formalize IUT IV's explicit estimates and its
  Diophantine corollaries.

Until these boxes are discharged, the defensible conclusion is: **the papers
state a complete claimed argument, but the disputed compatibility remains an
unverified prerequisite; the available Lean code demonstrates conditional
corridors and diagnostics, not a resolution of the controversy.**

## Verification log

- 2026-08-02: downloaded source page and selected original PDFs; recorded
  hashes above; extracted IUT III pages 174--184 and IUT IV introductory/
  dependency pages with `pypdf`.
- 2026-08-02: cloned/checked the five public repositories at the commits in the
  table; inspected their READMEs, ledgers, Stage-1/Cor312 files, and trust
  scripts. Full builds are recorded only when the command completes below.
- Pending: finish the current root `lake build` and run each repository's
  documented build/audit command; append the exact exit code and output here.
