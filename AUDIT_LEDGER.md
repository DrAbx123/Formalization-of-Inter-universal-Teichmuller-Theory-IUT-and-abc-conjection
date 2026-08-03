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

On 2026-08-04 the source layer was made reproducible and page-delimited with
`tools/extract_pdf_pages_text.py`. Search-oriented `plain` text and
placement-oriented `layout` text now cover both complete source PDFs, with
a continuous IUT III Theorem 3.11-to-Corollary 3.12 working text
(pp. 153--186, including the intervening Remarks 3.11.1--3.11.4), the earlier
shorter theorem/proof extract, and the semi-graph foundations (pp. 11--12, 20,
37--40). The source workflow uses the text layer first and returns to a rendered
page only for extraction conflicts, blocked typing/proof directions, or final
source-credit review. Exact hashes, extraction limitations, manually confirmed
formula directions, and the initial upstream/source classification are in
`papers/motizuki_corpus/SOURCE_TEXT_AUDIT.md`. Machine-extracted glyphs remain
an index rather than mathematical evidence on their own.

## Complete author-site corpus and citation map

The author-site crawl now lives under `papers/motizuki_corpus/`. It fetched the
eight entry pages (`papers-japanese.html`, `top-japanese.html`, CV, students,
thoughts, news, research, and travel), found 263 unique PDF links, and saved
262 files with SHA-256 hashes. One external link,
`~yuichiro/absolute_anabelian_cuspidalizations.pdf`, returned a confirmed 404
and is retained as a missing row in `pdfs.csv`; it is not silently omitted.
The downloaded corpus is about 644 MB and includes papers, comments, LaTeX
versions, lecture notes, and dated talk/slide PDFs linked from the site.

The bundled PDF workflow extracted 262 PDFs into `papers/motizuki_corpus/text/`
(8197 pages, about 14.8 million characters). The citation pass produced:

- `citation_edges.tsv`: 478 resolved label-to-file candidate edges;
- `reference_snippets.tsv`: 1449 bibliography snippets for manual review;
- `unresolved_reference_labels.tsv`: 112 unresolved historical labels;
- `DEPENDENCY_LAYERS.md`: the source-backed bottom-up layer plan.

The edges are evidence for reading order, not a proof of mathematical
dependency. In particular, the Tan introduction explicitly says to treat
anabelian/Frobenioid theory as prior material, read `EtTh` Sections 1--2, then
IUT I/II, and read IUT III carefully; IUT IV Section 1 can be read alongside
IUT III. This is now the basis for the Lean directory order.

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
| `LeanFormal/Archive/AnalysisExercise/Basic.lean` | **archived** (separate analysis exercise) | A real-analysis limit problem is fully checked and is unrelated to IUT. | It is outside the production entry point and must not be counted as IUT progress. |

The diagnostic therefore supports only: **the dispute is a missing/contested
identification or compatibility premise, not an arithmetic contradiction in the
abstract inequality.** It does not decide which side is mathematically right.

### Project hierarchy and proof boundary

The local project is now organized into deep, source-oriented modules rather
than one flat `IUT` directory. `LeanFormal/IUT/Project.lean` is the aggregate
entry point. The current hierarchy is:

- `Audit`: source hashes, status vocabulary, and obligation metadata;
- `Foundations/Arithmetic`, `Theta`, `Coordinates`, and `Volumes`: standard
  algebra, the square-exponent theta kernel and finite square-sum normalization, labelled real coordinates, and
  finite weighted-average lemmas;
- `IUTI/InitialTheta`, `IUTI/HodgeTheater`, `IUTII/Frobenioid`, and
  `IUTII/Kummer`:
  source obligations for the IUT I--II constructions;
- `Theorem311/Output` and `Theorem311/Indeterminacy/Ind1--Ind3`:
  Theorem 3.11 obligations plus the generic `Setoid`/`Quotient` transport
  kernel;
- `Corollary312/StepXI/IPL`, `SHE`, `APT`, and
  `HolomorphicHull/Volume`, `FiniteCertificateBridge`: the exact disputed wall;
- `ABCBridge/Statement`, `ABCBridge/UnprovedTarget`, and `ABCBridge/Bridge`: the standard ABC
  proposition, its explicit unfinished proof target, and the eventual bridge.

The following distinction is enforced in code:

| layer | current status | meaning |
|---|---|---|
| `Foundations/Arithmetic/FiniteLabels` | **proved** | `F_l = ZMod l`, prime/odd cardinality, sign involution, and the `{+/-1}` quotient are standard Mathlib constructions; the serial log and batch build contain no `sorryAx`. |
| `Foundations/Theta/GaussianKernel` | **proved** | Integer `j^2` symmetry, monoid special values, and the real logarithm lemma; this is only the algebraic kernel, not an etale theta function. |
| `Foundations/Theta/GaussianSquareSum` | **proved** | The finite `∑ j^2` closed form and the odd-label normalized factor `l(l+1)/12` are proved over `Real`; no theta function or IUT volume map is introduced. |
| `Foundations/Coordinates/RealLineTransport` | **proved** | Explicit positive-scale transports between copies of `Real`; equality is never silently identified across labels. `RealTransport.log_map` also proves the logarithmic additivity law for positive coordinates using Mathlib's `Real.log_mul`. |
| `IUTI/InitialTheta/ArithmeticData` | **interface with proved projections** | The IUT I arithmetic input is represented using Mathlib number fields, Galois/finite-dimensional field towers, `HasSqrtNegOne`, and Weierstrass elliptic curves with a puncture. The record is not an existence theorem and does not include the unconstructed reduction/anabelian/torsion data. |
| `Foundations/NumberField/FinitePlaceExtension` | **proved** | For a finite place above its contraction, the height-one prime is proved to lie over the lower prime; Mathlib's ramification theorem gives the valuation formula and uniform continuity on the dense valued fields. The induced map between actual adic completions is continuous and injective. Density and continuity extend the ramification formula to every completed element. The map restricts to an injective local homomorphism of completed valuation rings and induces an injective residue-field map. Tate uniformization is not inferred. |
| `Foundations/Geometry/ReductionBaseChange` | **proved** | Integral Weierstrass models map through commuting coefficient-ring/field squares. Integral equations with discriminant valuation one or unit `c4` are proved minimal. Good and multiplicative reduction are transported through the completion map; split multiplicative reduction is transported by the actual residue-field embedding and `Polynomial.Splits.map`. These are conditional preservation theorems, not proofs that the IUT input curve has the required reduction at any place. |
| `Foundations/Volumes/WeightedVolume` | **proved** | Finite weighted-average inequalities from ordinary ordered-field arithmetic. The file uses a minimal Mathlib import set; no local replacement for finite-sum machinery is introduced. |
| `IUTI/InitialTheta`, `IUTI/HodgeTheater`, `IUTII/Frobenioid`, `IUTII/Kummer` | **claim only / interface vocabulary** | These files register source obligations as metadata; they do not construct the paper's geometric objects. |
| `IUTII/Frobenioid/PrimeStripArithmetic` | **proved arithmetic kernel** | Finite interval prime-index set, primality projection, and interval monotonicity are proved with Mathlib's finite-order API; this is not an IUT Frobenioid prime strip. |
| `IUTII/Frobenioid/PrimeStripDegree` | **proved arithmetic kernel** | A finite family of ordinary commutative value monoids with official `MonoidHom` degree maps into `Multiplicative ℝ`; local multiplication and finite global degree additivity are proved. The data are not claimed to be an etale/Frobenioid realization. |
| `IUTI/HodgeTheater/PrimeStripCore` | **proved source-data kernel / realization pending** | `DPrimeStrip` and `FPrimeStrip` use Mathlib groups, surjective `MonoidHom`s, `Subgroup.ker`, `MulAut` actions, and the proved degree kernel. Forgetful maps, geometric kernels, action laws, and global degree laws compile and are axiom-audited; no arithmetic-geometric existence theorem is asserted. |
| `IUTI/HodgeTheater/HodgeTheaterCore` | **interface with proved link algebra** | A source-facing theater carries explicit initial arithmetic data, a concrete F-prime-strip carrier, and a finite theta packet. Prime-strip equivalence, theta-q/scale alignment, symmetry, composition, and three-theater source-to-target transport are proved. Existence of the paper's theaters, histories, anabelian reconstruction, and Hodge-Arakelov compatibility remain pending. |
| `IUTI/HodgeTheater/LocalPrimePlaces` | **proved local carrier kernel / realization pending** | Rational-prime labels, finite prime-interval labels, `ℚ_[p]`, algebraic-closure absolute Galois groups, the induced action on local units, and a nontrivial local q-parameter use Mathlib definitions. The projection is intentionally the identity because the etale fundamental-group quotient is not yet constructed. |
| `IUTII/Theta/FiniteThetaPacket` | **proved concrete lower packet / IUT identification pending** | A finite interval subtype supplies the standard Mathlib `Fintype`; the Gaussian packet is positive, nonzero, sign-symmetric, and has a proved finite log-volume identity. This is a lower numerical packet, not yet the paper's etale theta or Hodge-Arakelov object. |
| `IUTII/Theta/EtaleThetaQuotient` | **proved algebraic lower-central kernel / geometric realization pending** | The lower-central theta quotient, elliptic abelianization, exponent-`l` power quotients, canonical surjections, and central theta kernel are constructed with Mathlib commutator/normal-closure/QuotientGroup APIs. Profinite closedness, etale fundamental groups, and the rank-two arithmetic identification remain explicit obligations. |
| `IUTIII/Theorem311/*` | **claim only / interface vocabulary, with a proved generic kernel** | Theorem 3.11 output and Ind1--3 are tracked as obligations, not derived from number-field or elliptic-curve data. `Indeterminacy/QuotientTransport` proves representative-independent transport for arbitrary Setoids, but supplies no IUT-specific carriers or relations. |
| `IUTIII/Theorem311/Indeterminacy/OrbitTransport` | **proved group-action kernel** | Equivariant maps descend through Mathlib's official `MulAction.orbitRel` quotient, and a three-layer orbit transport has a representative formula. This is the Ind1/Ind2 mechanism, not the IUT-specific Galois/Kummer construction. |
| `IUTIII/Theorem311/Indeterminacy/UpperSemi` | **proved order kernel** | Set-valued upper-semi correspondences, singleton monotone maps, and composition are proved over standard preorders; this captures the logical direction of Ind3 without supplying the paper's log-Kummer correspondence. |
| `IUT_SUBTARGETS.md` | **research-target registry** | Separates proved Lean kernels, source-faithful IUT obligations, and external open-problem candidates; no candidate is counted as proved by the current project. |
| `IUTIII/Corollary312/StepXI/*` | **interface plus one marked `sorry`** | `cor312_of_constructed_stepXI` and the ordered corridor are proved from a supplied contract; `theorem311_produces_stepXI_contract` is the sole `sorryAx` reachable from the production entry point. `HolomorphicHull/Volume` additionally proves finite positive-packet determinant, tensor-product, rescaling, log-volume, and weighted-hull identities using the official `Matrix.det`, `Matrix.det_diagonal`, and `Finset` APIs. It does not construct the paper's holomorphic hull, local/global tensor normalization, or q-pilot objects. |
| `IUTIII/Corollary312/StepXI/FiniteCertificateBridge` | **interface** | `FiniteStepXILinkEvidence` makes `targetSigned`, IPL/SHE/APT evidence, and both comparison bounds explicit; from those supplied fields, Lean constructs a `StepXIContract` and proves the ordered conclusion. It does not prove any of the supplied source-facing fields. |
| `IUTIII/Corollary312/Routes` | **three claimed routes recorded / all pending** | The source-labelled Mochizuki 3.11.5 reorganization, Joshi's arithmetic-Teichmuller/Rosetta-Stone route, and Sarkisyan's explicitly claimed Erdos--Kac route are separate typed tags and audit obligations. No preprint result is imported as an axiom, and no route certificate is constructed. |
| `ABCBridge/Statement` | **proved statement layer** | `ABCConjecture` is the standard epsilon/constant radical proposition; the radical lemmas are checked against Mathlib. This is not a proof of the conjecture. |
| `ABCBridge/UnprovedTarget` | **sorry target** | The target is accepted only with the explicit `sorry`; it is not imported by the production project. |
| `Audit/Status.Obligation` | **proved audit metadata** | Obligations now carry optional `dependsOn`, `externalAxioms`, and named `sorryItems` lists; defaults preserve existing source metadata while key pending boundaries populate the lists explicitly. |
| `tools/check_no_custom_axioms.ps1` | **passed audit gate** | Scans production `LeanFormal/IUT` source for top-level `axiom`/`opaque` declarations; current result is zero. This is separate from the allowed, explicitly isolated `sorryAx` boundary. |
| `papers/motizuki_corpus/UPSTREAM_REUSE.md` | **provenance register** | Fixed commits and source surfaces for promachina, Takkun, LANA, com-junkawasaki, and PriestAmbrose are recorded with `proved`/`interface`/`diagnostic`/`external-claim` labels. It is a bibliography and reuse policy, not a mathematical intermediary layer. |

There is no production compatibility layer. The only files outside the
source-oriented dependency tree are under `Audit/Diagnostics`; they are
quarantined experiments and are not imported by `Project.lean`. This prevents
an old placeholder interface from silently becoming a dependency of the new
formalization.

### Reproducible verification record (2026-08-02)

| check | result | evidence |
|---|---|---|
| Original-source text reproducibility | **passed** | `logs/source-audit/run-20260804-020842/summary.json`; both source SHA-256 values match, both full pagewise extracts have all physical page markers, and the focused source extracts have 21/21 and 7/7 markers. The log explicitly sets `mathematicalProofClaim` to `false`. |
| Serial source-module audit | **27/27 exit code 0** | `logs/lean/serial-20260802-082127/summary.json`; every module was compiled with an explicit `.lake/build/lib/lean/...olean` output. |
| Production aggregate | **passed** | `logs/lean/run-20260802-083015.status.json`; `lake build LeanFormal`, `Build completed successfully (3027 jobs)`. |
| ABC without `sorry` | **expected failure** | `logs/lean/abc-20260802-082834/without-sorry.stderr.log`; unsolved `∃ K` goal, exit code 1. |
| ABC with `sorry` | **expected success** | `logs/lean/abc-20260802-082834/with-sorry.stdout.log`; exit code 0 and `sorryAx` in `#print axioms`. |
| Axiom sample | **passed audit** | `logs/lean/axioms-20260802-083444/axiom_audit.stdout.log`; foundational and conditional theorems have no `sorryAx`, while `theorem311_produces_stepXI_contract` explicitly depends on `sorryAx`. |
| Extended serial source-module audit | **28/28 exit code 0** | `logs/lean/serial-20260802-084418/summary.json`; includes the new `ABCBridge/Arithmetic/PrimitiveTriple.lean` module. |
| Current serial source-module audit | **29/29 exit code 0** | `logs/lean/serial-20260802-194319/summary.json`; includes `HolomorphicHull/Volume` and the current aggregate entry point. |
| Current serial source-module audit (quotient kernel) | **30/30 exit code 0** | `logs/lean/serial-20260802-200141/summary.json`; includes `Theorem311/Indeterminacy/QuotientTransport.lean`. |
| Current serial source-module audit (finite bridge) | **31/31 exit code 0** | `logs/lean/serial-20260802-201306/summary.json`; includes `StepXI/FiniteCertificateBridge.lean`. |
| Current logged aggregate | **passed** | `logs/lean/run-20260802-200751.status.json`; `lake build LeanFormal` completed successfully with 3034 jobs. |
| Current logged aggregate (explicit bridge) | **passed** | `logs/lean/run-20260802-201110.status.json`; `lake build LeanFormal` completed successfully after adding `FiniteCertificateBridge`. |
| Automated production axiom boundary | **passed** | `tools/check_axiom_boundary_logged.ps1` ran successfully; nested audit is `logs/lean/axioms-20260802-202110/`, and exactly one sampled production declaration has `sorryAx`: `theorem311_produces_stepXI_contract`. |
| Extended aggregate | **passed** | `lake build LeanFormal` reported `Build completed successfully (3028 jobs)` after adding the primitive-triple module. |
| Extended axiom sample | **passed audit** | `logs/lean/axioms-20260802-084337/axiom_audit.stdout.log`; `IsABCTriple.pairwise_coprime` has no `sorryAx`. |
| ABC radical factorization | **proved** | `IsABCTriple.radical_product_eq` was compiled in the aggregate build and has no `sorryAx`; latest sample is `logs/lean/axioms-20260802-085247/axiom_audit.stdout.log`. |
| Current ABC boundary audit | **expectations met** | `logs/lean/abc-20260802-194752/summary.json`: the no-`sorry` file exits 1 at the explicit existential target, while the marked-`sorry` file exits 0 and reports `sorryAx`. |
| Current automated axiom boundary | **passed** | `logs/lean/axioms-20260802-203000/axiom_audit.stdout.log`; `check_axiom_boundary_logged.ps1` found exactly one permitted production `sorryAx`. |
| Current serial source-module audit (square-sum normalization) | **32/32 exit code 0** | `logs/lean/serial-20260802-203032/summary.json`; includes `Foundations/Theta/GaussianSquareSum.lean`. |
| Current logged aggregate (square-sum normalization) | **passed** | `logs/lean/run-20260802-202838.status.json`; `lake build LeanFormal` completed successfully. |
| Current serial source-module audit (prime-strip arithmetic) | **33/33 exit code 0** | `logs/lean/serial-20260802-204318/summary.json`; includes `IUTII/Frobenioid/PrimeStripArithmetic.lean`. |
| Current logged aggregate (prime-strip arithmetic) | **passed** | `logs/lean/run-20260802-204147.status.json`; `lake build LeanFormal` completed successfully. |
| Current automated axiom boundary (prime-strip arithmetic) | **passed** | `logs/lean/axioms-20260802-204844/axiom_audit.stdout.log`; exactly one permitted production `sorryAx`. |
| Current logged aggregate (machine-readable obligation fields) | **passed** | `logs/lean/run-20260802-205422.status.json`; `lake build LeanFormal` completed successfully after adding the audit fields and Step-XI/ABC metadata. |
| Current axiom audit (machine-readable obligation fields) | **passed** | `logs/lean/axioms-20260802-205729/axiom_audit.stdout.log`; no new `sorryAx`. |
| Current automated axiom boundary (machine-readable obligation fields) | **passed** | `logs/lean/axioms-20260802-205754/axiom_audit.stdout.log`; exactly one permitted production `sorryAx`. |
| Current serial source-module audit (machine-readable obligation fields) | **33/33 exit code 0** | `logs/lean/serial-20260802-205820/summary.json`; all production modules compile independently. |
| Current logged aggregate (positive-coordinate log transport) | **passed** | `logs/lean/run-20260802-210716.status.json`; `lake build LeanFormal` completed successfully after proving `RealTransport.log_map`. |
| Current axiom audit (positive-coordinate log transport) | **passed** | `logs/lean/axioms-20260802-210900/axiom_audit.stdout.log`; `RealTransport.log_map` has only the standard Mathlib axioms, while the sole production `sorryAx` remains `theorem311_produces_stepXI_contract`. |
| Current automated axiom boundary (positive-coordinate log transport) | **passed** | `logs/lean/axioms-20260802-210916/axiom_audit.stdout.log`; exactly one permitted production `sorryAx`. |
| Current serial source-module audit (positive-coordinate log transport) | **33/33 exit code 0** | `logs/lean/serial-20260802-210947/summary.json`; all production modules, including `RealLineTransport`, compile independently. |
| Current standalone prime-strip degree check | **passed** | `lake env lean LeanFormal/IUT/IUTII/Frobenioid/PrimeStripDegree.lean`; the module compiles against the official `MonoidHom`/type-tag APIs. |
| Current serial source-module audit (prime-strip degree kernel) | **34/34 exit code 0** | `logs/lean/serial-20260802-222341/summary.json`; all production modules, including `PrimeStripDegree` and `Project.lean`, compile independently. |
| Current logged aggregate (prime-strip source-data kernel) | **passed** | `logs/lean/run-20260802-223830.status.json`; `lake build LeanFormal` completed successfully after adding `PrimeStripCore`. |
| Current automated axiom boundary (prime-strip source-data kernel) | **passed** | `logs/lean/axioms-20260802-223855/axiom_audit.stdout.log`; exactly one permitted production `sorryAx`, still `theorem311_produces_stepXI_contract`. |
| Current serial source-module audit (prime-strip source-data kernel) | **35/35 exit code 0** | `logs/lean/serial-20260802-223925/summary.json`; all production modules compile independently, including `PrimeStripCore` and `Project.lean`. |
| Current standalone orbit-transport check | **passed** | `lake env lean LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/OrbitTransport.lean`; official orbit quotient transport compiles without `sorry`. |
| Current logged aggregate (orbit quotient transport) | **passed** | `logs/lean/run-20260802-225647.status.json`; `lake build LeanFormal` completed successfully after adding `OrbitTransport`. |
| Current automated axiom boundary (orbit quotient transport) | **passed** | `logs/lean/axioms-20260802-225752/axiom_audit.stdout.log`; exactly one permitted production `sorryAx`. |
| Current serial source-module audit (orbit quotient transport) | **36/36 exit code 0** | `logs/lean/serial-20260802-225832/summary.json`; all production modules compile independently, including `OrbitTransport` and `Project.lean`. |
| Current custom-axiom declaration scan | **passed** | `tools/check_no_custom_axioms.ps1` reported `customAxiomDeclarations = 0`; no production top-level `axiom` or `opaque` declaration exists. |
| Current logged aggregate (upper-semi Ind3 kernel) | **passed** | `logs/lean/run-20260802-230942.status.json`; `lake build LeanFormal` completed successfully after adding `UpperSemi`. |
| Current automated axiom boundary (upper-semi Ind3 kernel) | **passed** | `logs/lean/axioms-20260802-231029/axiom_audit.stdout.log`; exactly one permitted production `sorryAx`. |
| Current serial source-module audit (upper-semi Ind3 kernel) | **37/37 exit code 0** | `logs/lean/serial-20260802-231053/summary.json`; all production modules compile independently, including `UpperSemi` and `Project.lean`. |
| Current serial source-module audit (initial arithmetic data) | **38/38 exit code 0** | `logs/lean/serial-20260802-232402/summary.json`; all production modules compile independently, including `InitialTheta/ArithmeticData` and `Project.lean`. |
| Current serial source-module audit (local prime-place carrier) | **39/39 exit code 0** | `logs/lean/serial-20260802-234942/summary.json`; all production modules compile independently, including `HodgeTheater/LocalPrimePlaces` and `Project.lean`. |
| Current arithmetic-data recheck after removing vacuous theorem | **passed** | `logs/lean/recheck-20260802-2330-arithmetic/ArithmeticData.log`; the source-facing record and Mathlib projections compile without the former `jInvariant_is_defined : True` placeholder. |
| Current axiom audit after arithmetic-data cleanup | **passed** | `logs/lean/recheck-20260802-2330-axioms/stdout.log`; the only sampled production `sorryAx` remains `theorem311_produces_stepXI_contract`. |
| Current custom-axiom declaration scan after arithmetic-data cleanup | **passed** | `tools/check_no_custom_axioms.ps1` reported `customAxiomDeclarations = 0`. |
| Current logged aggregate after arithmetic-data cleanup | **passed** | `logs/lean/run-20260802-233628.stdout.log`; `lake build LeanFormal` completed successfully (3066 jobs). |
| Current automated axiom boundary after arithmetic-data cleanup | **passed** | `logs/lean/axioms-20260802-233644/axiom_audit.stdout.log`; exactly one permitted production `sorryAx`, at `theorem311_produces_stepXI_contract`. |
| Current logged aggregate after local prime-place carrier | **passed** | `logs/lean/run-20260802-235652.stdout.log`; `lake build LeanFormal` completed successfully (3072 jobs). |
| Current automated axiom boundary after local prime-place carrier | **passed** | `logs/lean/axioms-20260802-235652/axiom_audit.stdout.log`; the local carrier declarations use only standard axioms and the sole production `sorryAx` remains `theorem311_produces_stepXI_contract`. |

### Public repositories checked at fixed commits

| repository (commit) | build/scope actually observed | status at the IUT wall |
|---|---|---|
| [promachina/iut-lean](https://github.com/promachina/iut-lean) `4953e647` | 128 Lean files. The project has an extensive Stage-1 source-facing layer and its own dependency/audit documents. `AlgorithmicOutput` stores `ipl`, `she`, `apt` as `Prop` fields; downstream `CorollarySchema`/`SourceObligations` prove the ordered comparison once certificates, a common-target bound, hull/measure data, and q-positivity are supplied. | **interface**. The repository README explicitly lists full Frobenioids, holomorphic hulls, determinants, and local-field/Haar compatibility as remaining construction work. A passing downstream theorem is conditional on those records. |
| [promachina/iut-lean](https://github.com/promachina/iut-lean) `02ab3ded` (current HEAD checked 2026-08-03) | 152 Lean files. Since `4953e647`, the source-facing layer adds etale-theta quotients, Galois image/complement carriers, source Frobenioid birationalization/dictionaries/factors, glued anabelioids and finite etale transitions, tempered covering/deck/recovery structures, and a much more detailed `SourceTheorem311`/Step-XI dependency audit. Its `lakefile.toml` pins Mathlib `v4.30.0`, whereas this production project uses Lean/Mathlib `4.32.2`; the definitions are therefore a reference for selective API migration, not a drop-in import. | **source interface with many proved local kernels; final wall still conditional**. The latest source code explicitly keeps algorithmic IPL/SHE/APT and several source endpoints as obligations/opaque fields. A standalone `Iut/Basic.lean` check was blocked before elaboration because Lake attempted to switch the external Mathlib checkout and encountered untracked package-worktree files; this is recorded as an environment/dependency-check limitation, not as a proof result. |
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
- 2026-08-02: added the deep source-oriented directory hierarchy, concrete
  finite-label/theta/coordinate/volume modules, and explicit ABC
  no-`sorry`/with-`sorry` boundary checks. The first parallel build exposed
  cache-read races and two Gaussian-kernel source errors; both errors were
  repaired, and the final serial run was clean.
- 2026-08-02: serial source audit completed with 27/27 exit code 0 in
  `logs/lean/serial-20260802-082127/`; the aggregate `lake build LeanFormal`
  completed with exit code 0 in `logs/lean/run-20260802-083015.status.json`.
- 2026-08-02: `verification/abc_without_sorry.lean` failed at its unsolved
  existential target as intended, while `abc_with_sorry.lean` passed and
  reported `sorryAx`; the exact outputs are in `logs/lean/abc-20260802-082834/`.
- 2026-08-02: `verification/axiom_audit.lean` passed. Its output records
  standard Mathlib axioms for the proved arithmetic layers and `sorryAx` only
  for `theorem311_produces_stepXI_contract`.
- 2026-08-02: added `ABCBridge/Arithmetic/PrimitiveTriple.lean`, proving from
  the standard gcd addition lemmas that every `IsABCTriple` is pairwise
  coprime, and proved the corresponding radical factorization using
  Mathlib's `UniqueFactorizationMonoid.radical_mul`; the updated 3028-job
  aggregate build and axiom audit both passed.
- 2026-08-02: replaced the provisional Step-(xi) volume arithmetic with a
  finite positive-packet kernel. Determinants are delegated to Mathlib's
  `Matrix.det` and `Matrix.det_diagonal`; tensor and rescaling laws use
  Mathlib's finite product/sum lemmas, and positivity is carried in the
  structure rather than assumed by an empty type or an arbitrary definition.
  Standalone compilation and the 3030-job aggregate build passed. The axiom
  audit is `logs/lean/axioms-20260802-194053/axiom_audit.stdout.log`: all new
  packet/hull declarations have no `sorryAx`; the only production `sorryAx`
  reachable from the production entry point remains
  `theorem311_produces_stepXI_contract`; the separately compiled
  `ABCBridge/UnprovedTarget.lean` is intentionally not imported there.
- 2026-08-02: added `Theorem311/Indeterminacy/QuotientTransport.lean`.
  `QuotientCompatibleMap.lift_mk` and the three-layer transport theorem are
  checked with the current `Quotient.map` API; the IUT-specific Ind1--Ind3
  data are still pending. The 3034-job aggregate and 30-module serial audit
  passed, and `logs/lean/axioms-20260802-200058/axiom_audit.stdout.log`
  records no `sorryAx` for the new declarations.
- 2026-08-02: added `StepXI/FiniteCertificateBridge.lean`. It makes the
  target value and IPL/SHE/APT evidence explicit before assembling the
  conditional contract; aggregate build and axiom audit passed, with the
  source-construction `sorryAx` unchanged.
- 2026-08-02: added `Foundations/Theta/GaussianSquareSum.lean`, proving the
  finite square-sum formula and the odd-label normalization
  `l(l+1)/12`. This is the arithmetic part of the normalization only; its
  geometric/IUT interpretation remains pending. The 32-module serial audit,
  aggregate build, and automated axiom boundary all passed.
- 2026-08-02: added `IUTII/Frobenioid/PrimeStripArithmetic.lean`. It proves
  finiteness and interval monotonicity for ordinary prime indices while
  keeping the actual Frobenioid prime-strip construction pending. The
  33-module serial audit, aggregate build, and axiom boundary all passed.
- 2026-08-02: extended `Audit.Status.Obligation` with machine-readable lower
  dependencies, external-axiom names, and named sorry items. The Step-XI
  contract and isolated ABC target now populate those fields explicitly; all
  aggregate, axiom, boundary, and 33-module serial checks passed.
- 2026-08-02: added and audited `RealTransport.log_map`. For a positive
  coordinate, the official Mathlib logarithm API proves that a positive-scale
  transport adds `log(scale)` to the coordinate log. The aggregate build,
  axiom audit, automated boundary check, and the 33-module serial audit all
  passed; this remains a coordinate kernel, not the paper's global log-volume
  comparison.
- 2026-08-02: added `IUTII/Frobenioid/PrimeStripDegree.lean`. Its local
  degree maps are standard `MonoidHom`s into `Multiplicative ℝ`, and the
  finite global degree laws are proved without a custom matrix or replacement
  algebra library. The module compiles standalone; the source-level
  Frobenioid and etale realization remains an explicit obligation.
- 2026-08-02: the first 34-module serial attempt was interrupted by an
  out-of-memory failure caused by a stale Lean language server, before any
  source diagnostic was emitted. After that background process was stopped,
  the complete rerun passed with 34/34 exit code 0 in
  `logs/lean/serial-20260802-222341/summary.json`.
- 2026-08-02: added `IUTI/HodgeTheater/PrimeStripCore.lean`. The module
  realizes the D/F prime-strip carrier layer and its `F → D → D⊢` bookkeeping
  with standard Mathlib groups, kernels, actions, and degree homomorphisms;
  the existence of such data from the paper's number field and elliptic curve
  is still pending. Aggregate, axiom-boundary, and 35-module serial checks
  passed (`logs/lean/serial-20260802-223830.status.json`,
  `logs/lean/axioms-20260802-223855/`, and
  `logs/lean/serial-20260802-223925/`).
- 2026-08-02: added `Theorem311/Indeterminacy/OrbitTransport.lean`.
  Equivariant maps now descend through Mathlib's official orbit quotient, and
  the three-layer representative formula is proved. This is a checked
  Ind1/Ind2 mechanism kernel; the IUT-specific Galois/Kummer links remain
  pending. The aggregate, boundary, and 36-module serial checks passed in
  `logs/lean/run-20260802-225647.status.json`,
  `logs/lean/axioms-20260802-225752/`, and
  `logs/lean/serial-20260802-225832/`.
- 2026-08-02: added `tools/check_no_custom_axioms.ps1`. It scans every
  production Lean source file for top-level `axiom`/`opaque` declarations and
  reports zero. The separate axiom audit continues to show only Lean's
  standard `propext`, `Classical.choice`, and `Quot.sound`, plus the one
  explicitly marked `sorryAx` at the Step-XI source-construction boundary.
- 2026-08-02: added `Theorem311/Indeterminacy/UpperSemi.lean`. The Ind3
  direction is now represented by a set-valued upper-semi correspondence;
  singleton monotone maps and composition are proved over standard preorders.
  The actual log-Kummer correspondence is still pending. Aggregate,
  axiom-boundary, and 37-module serial checks passed in
  `logs/lean/run-20260802-230942.status.json`,
  `logs/lean/axioms-20260802-231029/`, and
  `logs/lean/serial-20260802-231053/`.
- 2026-08-02: added `IUTI/InitialTheta/ArithmeticData.lean`. The source-facing
  prime/number-field/tower/elliptic-curve record now uses current Mathlib
  objects; it is explicitly an interface, not an existence theorem. A trivial
  `True` theorem was removed before the recheck so that the audit does not count
  vacuous declarations as progress. The 38-module serial audit passed in
  `logs/lean/serial-20260802-232402/summary.json`; the cleanup rechecks are in
  `logs/lean/recheck-20260802-2330-*/`.
- 2026-08-02: added `IUT_SUBTARGETS.md`, which records the recommended release
  ladder and distinguishes internal Step-XI obligations from genuinely open
  external candidates such as Hall-type and restricted Szpiro statements.
- 2026-08-03: added the concrete local prime-place carrier in
  `IUTI/HodgeTheater/LocalPrimePlaces.lean`. Rational prime labels, p-adic
  fields, local absolute Galois groups, their action on algebraic-closure
  units, and a nontrivial local q-parameter are all built from Mathlib; the
  etale fundamental-group and Frobenioid realization remain an explicit
  pending obligation.
- 2026-08-03: added `IUTII/Kummer/KummerPolynomial.lean`. The Mathlib
  `AdjoinRoot (X^n - C(a))` carrier, root-power identity, non-vanishing, and
  local p-adic specialization compile without new axioms; irreducibility,
  valuation/log structures, and the vertical correspondence remain pending.
- 2026-08-03: completed the warning cleanup. The changed-module recheck is
  `logs/lean/warning-audit/changed-modules.stdout.log`; it reports only the
  deliberately retained `sorry` at
  `LeanFormal/IUT/IUTIII/Corollary312/StepXI/Contract.lean:63`. The local
  universe-linter exception on `FPrimeStrip` preserves independent universes
  without changing the mathematical interface. `check_no_custom_axioms.ps1`
  reports zero top-level production `axiom`/`opaque` declarations, and the
  boundary audit `logs/lean/axioms-20260803-004830/` passes with exactly one
  expected `sorryAx`.
- 2026-08-03: the 40-module serial pass is recorded in
  `logs/lean/serial-20260803-002606/summary.json`. Four late modules first
  encountered transient missing Mathlib object files while the editor's Lean
  server was indexing; `Contract`, `Comparison`, `FiniteCertificateBridge`,
  and `IUT/Project` were then recompiled individually with exit code 0. No
  source error remains.
- 2026-08-03: corrected the PowerShell profile's stale hard-coded
  `D:\Miniconda3` hook. It now initializes Conda only if a known executable
  exists, so missing Miniconda cannot pollute every Lean command with a startup
  error.
- 2026-08-03: added `IUTII/Frobenioid/LocalPrimeStrip.lean` as the next
  bottom-up construction. It realizes `FPrimeStrip` over the actual rational
  prime places with local unit monoids in `PadicAlgCl p`, the absolute Galois
  action, and a logarithmic p-adic norm degree map. The degree proof uses
  Mathlib's `PadicAlgCl` norm and `Real.log_mul`; it does not claim integral
  Frobenioid, arithmetic-Frobenius, or etale realization. The standalone
  module, `VerticalCorrespondence` metadata, `IUT/Project`, and the axiom
  boundary all compile; the latest boundary log is
  `logs/lean/axioms-20260803-011714/` with the same single production
  `sorryAx`.
- 2026-08-03: added `IUTII/Kummer/RootRealization.lean` as the explicitly
  smaller `AdjoinRootEmbedding` kernel, not as the paper's full
  `KummerRootRealization` or vertical correspondence. Mathlib's universal
  `AdjoinRoot.liftAlgHom` maps the formal root to an explicitly chosen root in
  the algebraic closure of a local p-adic field, and Lean proves the root
  equation and non-vanishing. The public source implementations additionally
  require compatible rational-root systems, Galois root ratios, unit quotients,
  and cocycle laws; those remain pending here, as do irreducibility, finite
  degree, Frobenioid compatibility, and the vertical log-Kummer construction.
  The dependency graph and audit entry label this distinction explicitly.
- 2026-08-03: completed the first source-faithful Kummer batch. The new
  `CompatibleRoots`, `KummerRootRatio`, and `VerticalLogKummer` modules, the
  existing `VerticalCorrespondence` metadata, and `IUT/Project.lean` compile
  serially with exit code 0. The batch has no new linter warnings; the axiom
  audit shows only Lean's standard `propext`, `Classical.choice`, and
  `Quot.sound`, with the pre-existing single `sorryAx` at the Step-XI source
  construction. `check_no_custom_axioms.ps1` reports zero custom declarations
  (`logs/lean/warning-audit/` and the 2026-08-03 audit output).
- 2026-08-03: reran the Kummer batch trust-boundary checks serially after the
  source build. `run_axiom_audit_logged.ps1` passed at
  `logs/lean/axioms-20260803-020318/`; the stricter boundary check passed at
  `logs/lean/axioms-20260803-020341/`, with exactly one expected
  `sorryAx` (`theorem311_produces_stepXI_contract`) and zero custom
  `axiom`/`opaque` declarations.
- 2026-08-03: added `IUTII/Kummer/NatRootSystem.lean`. This source-facing
  lower layer uses the unit-group carrier for Kummer roots, proves the
  root-of-a-power identity, constructs compatible roots in an algebraic
  closure by a factorial chain, and proves the telescope and compatibility
  laws. The serial Kummer/project batch passed; the boundary audit passed at
  `logs/lean/axioms-20260803-021325/` with the same single expected
  `sorryAx`, and `check_no_custom_axioms.ps1` remains at zero.
- 2026-08-03: added `IUTII/Kummer/KummerClass.lean`. A Galois action on the
  unit group now acts on cyclotomic towers, and Lean proves the unit-valued
  Kummer class, its identity and crossed multiplication laws, and the
  change-of-root coboundary equation. This is still below the paper's full
  H¹/Kummer-isomorphism and ramification statements; no such result is being
  inferred from this kernel. The seven-module Kummer/project batch passed
  with no warnings in `logs/lean/serial-20260803-022657/summary.json`.
  The axiom audit passed at `logs/lean/axioms-20260803-022841/`, the strict
  boundary check passed at `logs/lean/axioms-20260803-022950/`, and the scan
  for custom top-level axioms/opaques remains zero.
- 2026-08-03: made the bounded integer `SignedLabel` carrier a standard
  Mathlib finite interval subtype and supplied its noncomputable `Fintype`
  instance. Added `IUTII/Theta/FiniteThetaPacket.lean`, which constructs the
  real Gaussian theta packet on these labels and proves positivity,
  nonvanishing, `j ↦ -j` symmetry, the logarithmic special-value formula, and
  finite-sum invariance. This packet is a concrete lower object; it is not
  asserted to be the paper's etale theta function or Hodge-Arakelov output.
  The affected lower/Kummer/project rebuild completed without warnings across
  `logs/lean/serial-20260803-025407/` and
  `logs/lean/serial-20260803-025721/`. The audit is recorded at
  `logs/lean/axioms-20260803-025850/`, the strict boundary at
  `logs/lean/axioms-20260803-025912/`, and custom top-level axiom count is 0.
- 2026-08-03: changed the logged Lean batch and axiom-audit scripts to pass
  `-j 1`. This is a deterministic build setting that avoids cache-lock
  contention with the editor's background workers; it does not add an axiom
  or alter any mathematical declaration.
- 2026-08-03: added `IUTIII/Corollary312/StepXI/ThetaPacketBridge.lean`.
  The concrete finite Gaussian theta packet now converts into the existing
  positive finite-packet carrier used by determinant, tensor, logarithm, and
  rescaling proofs. The bridge proves the product/log-determinant and sign
  invariance transport, as well as the rescaling identities, without adding a
  new matrix implementation or an existence assumption for a hull. The
  Volume/bridge/certificate/project batch passed without warnings in
  `logs/lean/serial-20260803-030448/summary.json`; the audit passed at
  `logs/lean/axioms-20260803-030613/`, the boundary at
  `logs/lean/axioms-20260803-030636/`, and custom axiom count remains zero.
- 2026-08-03: added `IUTI/HodgeTheater/HodgeTheaterCore.lean`. The source-facing
  Hodge-theater carrier now explicitly combines Initial Theta arithmetic data,
  an F-prime-strip carrier, and the finite theta packet. Link symmetry,
  composition, and three-theater source-to-target q/scale transport are
  proved using the official equivalence APIs. The arithmetic/geometric
  existence and Hodge-Arakelov/anabelian compatibility are still interface
  obligations. The affected batch (including `Project.lean`) passed with no
  warnings; the standalone entry check is recorded by the batch logs under
  `logs/lean/serial-20260803-032137/` and
  `logs/lean/project-hodge-routes.stderr.log`.
- 2026-08-03: added `IUTIII/Corollary312/Routes.lean` and registered a third
  claimed route, Mikael Sarkisyan's Erdos--Kac preprint
  ([arXiv:2306.02448](https://arxiv.org/abs/2306.02448)). The route is marked
  pending and isolated from the Mochizuki 3.11.5 and Joshi routes. The
  Mochizuki report explains that "3.11.5" is a reorganization checkpoint,
  not an original theorem number; this source distinction is preserved in the
  obligation note.
- 2026-08-03: reran the production trust-boundary checks after the Hodge and
  route batch. `verification/axiom_audit.lean` passed at
  `logs/lean/axioms-20260803-032451/`; the automated boundary passed with
  exactly one permitted production `sorryAx`, and
  `tools/check_no_custom_axioms.ps1` reported zero custom declarations.
- 2026-08-03: refreshed the `promachina/iut-lean` reference to GitHub HEAD
  `02ab3deda6b296f74257138c28ff25ecb51aac67` (152 Lean files). The new source
  modules were inspected for the Hodge-theater, etale-theta, Frobenioid,
  Galois, glued-anabelioid, tempered-covering, and Theorem 3.11 surfaces.
  They materially improve the source-facing dependency map and are now the
  preferred upstream reference. They remain outside `LeanFormal/IUT` until
  each module is ported to Mathlib 4.32.2 and passes this project's axiom and
  source-status audit. The upstream standalone check was attempted but Lake
  stopped at its pinned Mathlib `v4.30.0` package checkout because that
  external package worktree contained untracked files; no upstream theorem
  was counted as compiled here.
- 2026-08-03: the complete production serial rebuild passed 51/51 with
  `-j 1` in `logs/lean/serial-20260803-033102/summary.json`; the root
  `LeanFormal.lean` entry passed in `logs/lean/root-20260803-0341.stdout.log`,
  and the final axiom/boundary/custom-axiom audit passed in
  `logs/lean/axioms-20260803-034136/` with exactly one expected `sorryAx`.
- 2026-08-03: ported the upstream source-facing etale-theta lower-central
  quotient kernel into `IUTII/Theta/EtaleThetaQuotient.lean` using the current
  Mathlib quotient-group and commutator APIs. The port is algebraic and
  source-labelled; it does not assert the profinite/etale realization or the
  `(Z/lZ)^2` arithmetic identification.
- 2026-08-03: the etale-theta quotient batch passed 6/6 with no diagnostics in
  `logs/lean/serial-20260803-035204/summary.json`. The final axiom sample and
  strict boundary passed in `logs/lean/axioms-20260803-035408/` and
  `logs/lean/axioms-20260803-035424/`; the sole production `sorryAx` remains
  `theorem311_produces_stepXI_contract` and custom top-level axiom count is 0.
- 2026-08-03: cross-indexed the current upstream repositories for reusable
  conclusions. `promachina/iut-lean` supplies the most detailed source
  constructions and theorem-3.11/Step-XI audit surfaces; `Takkun-IUT_LEAN`
  supplies independently useful finite/group/log-volume kernels and explicit
  diagnostics (`Multiradial/IdentificationAudit` and
  `TranscriptionDegeneracy`) that must not be mistaken for a Corollary 3.12
  proof; `iut4-sec1` supplies elementary IUT-IV Section-1 arithmetic only.
  Reuse is now recorded by commit and status, with version-adaptation work
  separated from mathematical proof obligations.
- 2026-08-03: completed the bottom-layer refactor requested for the
  Corollary 3.12 prerequisites. `Foundations/Arithmetic/Radical`,
  `PrimitiveAdditive`, `PrimeIntervals`, and `PrimeLabels` now provide one
  shared radical/triple/finite-prime-label vocabulary; `Foundations/Geometry`
  provides a concrete Mathlib Weierstrass model with prescribed `j` and the
  punctured elliptic carrier; and `Foundations/LinearAlgebra/FiniteDeterminant`
  proves diagonal determinant, tensor-product, rescaling, and positive finite
  log-product identities. These are ordinary mathematical kernels, not
  constructions of Frobenioids, Hodge theaters, or holomorphic hulls.
- 2026-08-03: the fresh independent source-module audit passed `59/59` with
  zero failed modules in
  `logs/lean/serial-20260803-053739/summary.json`. The logged aggregate build
  passed with `Build completed successfully (3145 jobs)` in
  `logs/lean/aggregate-20260803-060943.stdout.log`; its only production warning
  relevant to trust is the deliberate `sorry` in
  `IUTIII/Corollary312/StepXI/Contract.lean:63` (the other messages are
  linter/header warnings).
- 2026-08-03: the trust-boundary batch was rerun with persistent logs. The
  axiom sample is `logs/lean/axiom-audit-20260803-061306.log` and contains only
  `propext`, `Classical.choice`, and `Quot.sound` for the lower kernels; the
  sole production `sorryAx` is
  `LeanFormal.IUT.theorem311_produces_stepXI_contract`. The strict boundary
  check passed with `sorryAxLines = 1` in
  `logs/lean/boundary-20260803-061501.log` (nested audit
  `logs/lean/axioms-20260803-061502/`), the custom
  top-level axiom scan is
  `logs/lean/custom-axiom-20260803-061307.log` with `customAxiomDeclarations =
  0`, and the isolated ABC checks are
  `logs/lean/abc-without-sorry-20260803-061307.log` (expected unsolved target,
  exit 1) and `logs/lean/abc-with-sorry-20260803-061307.log` (exit 0 with an
  explicit `sorryAx`).
- 2026-08-03: extracted `Foundations/Arithmetic/NormLog.lean`, a generic
  `NormedField` unit norm/log `MonoidHom`, and refactored
  `IUTII/Frobenioid/LocalPrimeStrip.lean` to instantiate it. The generic module
  and the refactored local carrier compile independently; the only repair was
  the explicit `noncomputable` marker required by the definition's use of
  `Real.log`. No new axiom or `sorryAx` was introduced.
- 2026-08-03: the post-`NormLog` independent source audit passed `60/60` with
  no failed modules in `logs/lean/serial-20260803-062038/summary.json`.
  The persistent aggregate log
  `logs/lean/aggregate-20260803-063322.stdout.log` records
  `Build completed successfully (3146 jobs)` and exit code 0; it includes both
  the new generic module and the refactored local p-adic carrier.
- 2026-08-03: the refreshed trust gates passed. The full axiom sample is
  `logs/lean/axiom-audit-20260803-063523.log`; the new norm/log declarations
  use only standard Lean/Mathlib axioms and the only production `sorryAx`
  remains `theorem311_produces_stepXI_contract`. The strict boundary output is
  `logs/lean/boundary-20260803-063549.log` with `sorryAxLines = 1`, and the
  custom declaration scan is `logs/lean/custom-axiom-20260803-063549.log` with
  `customAxiomDeclarations = 0`. The isolated ABC checks remain deliberately
  split: `logs/lean/abc-without-sorry-20260803-0636.log` exits 1 at the
  existential constant target, while
  `logs/lean/abc-with-sorry-20260803-0636.log` exits 0 and reports `sorryAx`.
- 2026-08-03: added `Foundations/Arithmetic/PadicValuation.lean`. It records
  Mathlib's natural-number prime valuation self-value, multiplication and
  power laws, prime-support equivalence, and prime-power divisibility
  characterization. The standalone logged compile passed at
  `logs/lean/padic-valuation-20260803-0639.log`; the module contains no IUT
  object, local-field existence assumption, ABC estimate, or `sorry`.
- 2026-08-03: the affected production entry compiled at
  `logs/lean/project-padic-valuation-20260803-0641.log`, and the logged
  aggregate passed with `Build completed successfully (3147 jobs)` in
  `logs/lean/aggregate-20260803-064015.stdout.log`. The new valuation sample
  appears in `logs/lean/axiom-audit-20260803-064208.log` with only standard
  Lean/Mathlib axioms. The strict boundary and custom-declaration gates passed
  in `logs/lean/boundary-20260803-064236.log` and
  `logs/lean/custom-axiom-20260803-064236.log`; exactly one production
  `sorryAx` remains at the unchanged Step-XI contract constructor.
- 2026-08-03: removed two unused `DecidableEq` hypotheses from the finite
  log-product lemmas and normalized the production entry's copyright header.
  The affected finite-determinant, Step-XI volume, and project checks all pass.
  The final aggregate log for this batch is
  `logs/lean/aggregate-20260803-064712.stdout.log`: exit 0,
  `Build completed successfully (3147 jobs)`, with the deliberate Step-XI
  `sorry` as its only warning. The final strict boundary and custom-axiom
  scans are `logs/lean/boundary-20260803-064904.log` and
  `logs/lean/custom-axiom-20260803-064905.log`.
- 2026-08-03: ported the finite/infinite number-field-place prerequisite from
  the current `promachina/iut-lean` source map into two smaller Mathlib 4.32.2
  foundation files. `Foundations/NumberField/FinitePlaces.lean` uses the
  official `FinitePlace.maximalIdeal` equivalence, constructs the residue
  quotient and residue characteristic, proves the quotient finite and the
  characteristic prime/positive, contracts height-one primes along field
  extensions, and proves restriction transitive in towers.
  `Foundations/NumberField/Places.lean` forms the disjoint finite/infinite
  carrier, uses Mathlib's infinite-place embedding composition, and proves the
  combined restriction transitive. No selected/bad/good place set, elliptic
  reduction, or Tate parameter is supplied.
- 2026-08-03: the number-field-place targeted serial audit passed `3/3` in
  `logs/lean/serial-20260803-070026/summary.json`. The aggregate build passed
  with `Build completed successfully (3646 jobs)` in
  `logs/lean/aggregate-20260803-070123.stdout.log`. The axiom sample
  `logs/lean/axiom-audit-20260803-070315.log` shows only `propext`,
  `Classical.choice`, and `Quot.sound` for the new theorems. The strict
  boundary passed in `logs/lean/boundary-20260803-070344.log` with the same one
  permitted Step-XI `sorryAx`; the custom declaration scan
  `logs/lean/custom-axiom-20260803-070344.log` reports zero.
- 2026-08-03: added
  `Foundations/Geometry/LocalReduction.lean`. It lifts Mathlib's good,
  multiplicative, and split multiplicative reduction classes from a chosen
  minimal Weierstrass equation to existential, presentation-independent
  predicates. Coordinate-change invariance, invariance under Mathlib's chosen
  minimal model, compatibility with mapping a variable change, and the
  split-multiplicative-to-multiplicative implication are proved. The
  source-facing predicates at a finite place use the actual adic completion
  and its valuation ring. No existence of good/stable/split multiplicative
  reduction at an IUT place, no preservation theorem along place restriction,
  and no Tate parameter is asserted.
- 2026-08-03: the local-reduction single-module log is
  `logs/lean/local-reduction-20260803-070814.stdout.log` (exit 0; empty output
  means no Lean diagnostics). The dependency-chain serial audit passed `4/4`
  in `logs/lean/serial-20260803-070913/summary.json`. The production aggregate
  passed with `Build completed successfully (3649 jobs)` in
  `logs/lean/aggregate-20260803-071039.stdout.log`. The new axiom samples in
  `logs/lean/axioms-20260803-071133/axiom_audit.stdout.log` use only
  `propext`, `Classical.choice`, and `Quot.sound`. The strict boundary log
  `logs/lean/boundary-20260803-071133.log` still reports exactly the one
  permitted Step-XI `sorryAx`; `logs/lean/custom-axiom-20260803-071133.log`
  reports zero custom top-level declarations.
- 2026-08-03: added
  `Foundations/NumberField/LocalQParameter.lean`. For each actual number-field
  finite completion, the completed DVR supplies an irreducible element and
  hence a nonzero q-candidate with valuation strictly below one. The file
  proves nontriviality (`q != 1`), positivity of the associated integral and
  natural-valued order, and closure under positive powers. The name
  `FinitePlaceQCandidate` is intentional: no theorem identifies this element
  with the Tate parameter of a specified elliptic curve. Tate uniformization,
  Galois equivariance, and equality with the curve's local height remain a
  separate `pending` audit obligation.
- 2026-08-03: the warning-free local q-parameter compile is
  `logs/lean/local-q-parameter-20260803-072135.stdout.log`; earlier failed
  elaboration attempts remain under the same `local-q-parameter-*` prefix for
  debugging history. The affected dependency chain passed `5/5` in
  `logs/lean/serial-20260803-072311/summary.json`, and the aggregate passed
  with `Build completed successfully (3650 jobs)` in
  `logs/lean/aggregate-20260803-072446.stdout.log`. The representative
  existence and positivity theorems use only `propext`, `Classical.choice`,
  and `Quot.sound` in
  `logs/lean/axioms-20260803-072536/axiom_audit.stdout.log`. The strict
  boundary and custom declaration gates passed in
  `logs/lean/boundary-20260803-072536.log` and
  `logs/lean/custom-axiom-20260803-072536.log`.
- 2026-08-03: added
  `Foundations/Geometry/EllipticTorsion.lean`. It constructs the actual
  `l`-torsion subgroup of the closure-valued elliptic point group, the
  absolute-Galois action, its identity/composition laws, open point
  stabilizers, and the induced `ZMod l`-linear/general-linear
  representations. Conditional on an actual basis `(ZMod l)^2 ~= E[l]`, it
  constructs the matrix representation, proves its kernel open and the
  representation continuous, constructs the fixed kernel field, and proves
  that field finite Galois (and a number field over a number-field base).
  Existence of the rank-two basis, rationality of all 6-torsion, and the
  source's `SL(2)` large-image condition are explicitly not proved.
- 2026-08-03: the final warning-free elliptic-torsion module log is
  `logs/lean/elliptic-torsion-20260803-073405.stdout.log`; earlier
  `elliptic-torsion-*` logs retain the Mathlib import/API adaptation history.
  The affected geometric chain passed `4/4` in
  `logs/lean/serial-20260803-073457/summary.json`; the aggregate passed with
  `Build completed successfully (3652 jobs)` in
  `logs/lean/aggregate-20260803-073611.stdout.log`. All five new action,
  openness, matrix, continuity, and fixed-field samples use only `propext`,
  `Classical.choice`, and `Quot.sound` in
  `logs/lean/axioms-20260803-073701/axiom_audit.stdout.log`. The strict
  boundary and custom declaration logs are
  `logs/lean/boundary-20260803-073701.log` and
  `logs/lean/custom-axiom-20260803-073701.log`.
- 2026-08-03: strengthened the number-field place layer with actual
  lying-over. `NumberFieldFinitePlace.comap_surjective` applies Going-Up to
  the integral extension of rings of integers, turns an upstairs maximal
  ideal into a height-one prime, and proves that its finite-place contraction
  is the requested lower place. Together with Mathlib's extension theorem for
  infinite places, `NumberFieldPlace.restrictionSection` chooses a full place
  section. Its image is a concrete selected-place set, and restriction is
  proved to give an equivalence from that image to all lower places. The
  section is noncanonical, as in the source choice; no `V_mod^bad` subset or
  reduction hypothesis is inferred from it.
- 2026-08-03: the standalone finite-place and full-section logs are
  `logs/lean/finite-place-surjective-20260803-074058.stdout.log` and
  `logs/lean/place-section-20260803-074306.stdout.log`. The affected number
  field chain passed `4/4` in
  `logs/lean/serial-20260803-074345/summary.json`; the aggregate passed with
  `Build completed successfully (3652 jobs)` in
  `logs/lean/aggregate-20260803-074502.stdout.log`. Lying-over, section
  injectivity, and selected-image equivalence use only `propext`,
  `Classical.choice`, and `Quot.sound` in
  `logs/lean/axioms-20260803-074605/axiom_audit.stdout.log`. The strict
  boundary/custom scans passed in `logs/lean/boundary-20260803-074604.log`
  and `logs/lean/custom-axiom-20260803-074604.log`.
- 2026-08-03: added
  `Foundations/NumberField/FinitePlaceExtension.lean`. An upper finite place is
  proved to lie over its contraction, and the ramification-index identity
  `v(x)^e = w(algebraMap x)` is imported from Mathlib's height-one valuation
  theorem. The valued-field algebra map is uniformly continuous and extends
  to a continuous injective ring homomorphism `k_v -> K_w`; its formula on the
  dense copy of `k` is proved. Continuity of both completed valuations and
  density of `k` then extend the ramification formula to every element of
  `k_v`. The local-field map preserves the completed valuation rings and
  induces an injective ring homomorphism between them. Reduction-type
  preservation and a Tate-parameter comparison remain unproved.
- 2026-08-03: the first continuity/injectivity elaboration failure is retained
  in `logs/lean/finite-place-extension-20260803-075451.stdout.log`; it records
  the Mathlib API adaptation that required an explicit lower-field argument.
  The corrected first standalone compile is
  `logs/lean/finite-place-extension-20260803-075537.stdout.log`. Failed
  notation/scoped-topology adaptation attempts for the completed valuation
  formula are retained in the `080358` and `080438` logs; the final extended
  module compiles in
  `logs/lean/finite-place-extension-20260803-080832.stdout.log`. The affected
  chain passed `6/6` in
  `logs/lean/serial-20260803-075619/summary.json`, and the full production build
  passed with `Build completed successfully (3654 jobs)` in
  `logs/lean/run-20260803-075822.stdout.log`. The five new axiom samples use
  only `propext`, `Classical.choice`, and `Quot.sound` in
  `logs/lean/axioms-20260803-075914/axiom_audit.stdout.log`. The strict boundary
  remains exactly one pre-existing Step-XI `sorryAx` in
  `logs/lean/boundary-20260803-075914.log`, while
  `logs/lean/custom-axiom-20260803-080002.log` reports zero custom top-level
  declarations with an explicit exit code 0.
- 2026-08-03: after extending the ramification formula to all completed
  elements and constructing the valuation-ring map, the final affected chain
  passed `6/6` in `logs/lean/serial-20260803-080949/summary.json`. The full
  build again passed `3654 jobs` in
  `logs/lean/run-20260803-081135.stdout.log`. The completed valuation formula,
  integrality preservation, and valuation-ring injectivity use only `propext`,
  `Classical.choice`, and `Quot.sound` in
  `logs/lean/axioms-20260803-081238/axiom_audit.stdout.log`. The boundary log
  `logs/lean/boundary-20260803-081238.log` still contains exactly the one
  pre-existing Step-XI `sorryAx`; the explicit-exit custom scan
  `logs/lean/custom-axiom-20260803-081304.log` reports zero declarations.
- 2026-08-03: strengthened `FinitePlaceExtension.lean` with the commuting
  square between the completed field and valuation-ring maps, proved the
  valuation-ring homomorphism local, constructed the induced residue-field
  homomorphism, proved its quotient-map formula, and proved it injective. The
  post-extension dependency chain passed `6/6` in
  `logs/lean/serial-20260803-082343/summary.json`; the full build, axiom,
  boundary, and custom-declaration evidence is in
  `logs/lean/run-20260803-082536.status.json`,
  `logs/lean/axioms-20260803-082633/axiom_audit.stdout.log`,
  `logs/lean/boundary-20260803-082633.log`, and
  `logs/lean/custom-axiom-20260803-082633.log`.
- 2026-08-03: added `Foundations/Geometry/ReductionBaseChange.lean`. Lean now
  proves integral-model transport, minimality from discriminant valuation one,
  and minimality from unit `c4`. Good and multiplicative reduction pass to an
  upper finite-place completion. For split multiplicative reduction, the
  integral models and reduced curves commute with the residue-field map, and
  the tangent-cone polynomial remains split by `Polynomial.Splits.map`.
  These are conditional preservation theorems; no lower reduction hypothesis
  for a specified IUT curve and no Tate uniformization is asserted.
- 2026-08-03: failed reduction/API checks remain under
  `logs/lean/reduction-base-change-check-*`,
  `multiplicative-base-change-check-*`, and `split-base-change-check-*`; the
  final successful checks are the `083648`, `084701`, and `085622` runs. The
  production chain passed `7/7` in
  `logs/lean/serial-20260803-090015/summary.json`, and the full build completed
  `3655 jobs` in `logs/lean/run-20260803-090222.stdout.log`. All new samples
  use only `propext`, `Classical.choice`, and `Quot.sound` in
  `logs/lean/axioms-20260803-090331/axiom_audit.stdout.log`. The strict boundary
  remains one Step-XI `sorryAx` in `logs/lean/boundary-20260803-090331.log`,
  while `logs/lean/custom-axiom-20260803-090331.log` reports zero custom
  top-level declarations.
