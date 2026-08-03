# IUT Lean Formalization

This repository is an exploratory Lean 4 formalization project for Shinichi
Mochizuki's inter-universal Teichmuller theory (IUT), with special attention to
the disputed implication around [IUT III, Corollary 3.12]. The goal is not to
assume that IUT is correct or incorrect. The goal is to make the relevant
objects, transports, indeterminacies, and real-valued comparisons explicit enough
that Lean can check whether the claimed implication is valid under stated
hypotheses.

The tracked `docs/` folder contains Markdown conversions of the four IUT papers,
Mochizuki's formalization progress reports, the Scholze-Stix critique, and
related source papers used as the local research corpus. The tracked research
draft is `paper/IUT_FORMALIZATION_3_12_DRAFT.tex`, with the rendered PDF at
`paper/IUT_FORMALIZATION_3_12_DRAFT.pdf`.

## Current Understanding

IUT studies number fields equipped with elliptic curves by constructing
Theta-Hodge theaters: "miniature models" of scheme theory in which the additive
and multiplicative aspects of arithmetic geometry are deliberately separated.
The horizontal Theta-links identify Frobenioid-theoretic multiplicative data
across theaters in a way that is not a ring or scheme morphism. The vertical
log-links, Kummer theory, and anabelian reconstruction machinery are then used to
recover enough information about "alien" arithmetic holomorphic structures to
produce log-volume estimates.

The original four papers were published in PRIMS in 2021. EMS lists IUT IV as
published on 5 March 2021 and tags its central vocabulary with terms such as
non-interference, Kummer-detachment, indeterminacy, q-pilot, Theta-pilot,
multiradial container, holomorphic hull, and species/mutation:
https://ems.press/journals/prims/articles/201528

The final arithmetic output is Theorem A of IUT IV: a class of Diophantine
inequalities from which Vojta for hyperbolic curves, abc, and Szpiro are claimed
to follow. The immediate technical bottleneck is earlier: IUT III, Theorem 3.11
is supposed to provide a multiradial representation for Theta-pilot objects, and
Corollary 3.12 is supposed to turn this into the estimate
`-|log(Theta)| >= -|log(q)|`.

## The Main Dispute

Scholze and Stix isolate the critical issue near IUT III, Corollary 3.12. In
their simplification, the categories of prime strips and realified Frobenioids
become canonically comparable enough that the crucial Theorem 3.11 data becomes
trivial rather than false. Their objection is that, once all copies of the real
line are consistently identified, the `j^2` scaling needed on the Theta side
cannot be inserted without monodromy/inconsistency; omitting those scalars leaves
an empty inequality. Their report is here:
https://www.math.uni-bonn.de/people/scholze/WhyABCisStillaConjecture.pdf

Mochizuki's response, as reflected both in IUT III and the April 2026 report, is
that this simplification erases the essential feature of the proof: the use of
Hodge theaters, log-links, Kummer-detachment, multiradial containers, and
indeterminacies to compare data while not identifying the ring/scheme histories
that must remain separated. In his current formalization plan, the first target
is exactly Stage 1: formalize the implication from IUT III, Theorem 3.11 to
Corollary 3.12, then work backward to the proof of Theorem 3.11 and the
supporting anabelian/Frobenioid/theta-function infrastructure.

That makes the Lean task precise: we need a formal object language in which the
labels, forgotten labels, allowed identifications, indeterminacy actions,
holomorphic hulls, log-volume maps, and real-line comparisons are all explicit.
If the hypotheses are too weak, Lean should expose the gap. If Mochizuki's
claimed "common container" logic is sufficient, Lean should expose the exact
extra structure that makes it sufficient.

## Related Formalization Efforts

Mochizuki's April 2026 progress report describes "LeanForm" primarily as a
communication and disambiguation tool, not only as a verifier. His proposed
stages are:

1. IUT III, Theorem 3.11 implies Corollary 3.12.
2. The proof of IUT III, Theorem 3.11 modulo IUT I-II.
3. IUT I-II modulo earlier anabelian geometry, Frobenioid, and theta-function
   results.
4. The earlier 1995-2015 background corpus.
5. The numerical/log-volume aspects of IUT IV and explicit estimates.

The public slides are available here:
https://aitpm.github.io/slides/Mochizuki.pdf

The LANA project was announced by ZEN Mathematics Center on 31 March 2026.
LANA stands for "Lean for ANAbelian geometry". Its stated aims are to formalize
major theorems of anabelian geometry in Lean, build a corresponding library, and
verify IUT through Lean formalization. ZEN reports that the project has been
underway since autumn 2023, with active operation from September 2024, and that
it intends to stay neutral while distinguishing genuine gaps from current
limitations of understanding. Core members named in the announcement are
Fumiharu Kato, Johan Commelin, Kiran Kedlaya, Yuichiro Hoshi, and Adam Topaz:
https://zen.ac.jp/news/zmcpostevent0331e

ZEN also announced an interim LANA progress report for 17 July 2026. As of this
README's creation on 27 May 2026, that report is still in the future.

Other relevant work includes Taylor Dupuy and Anton Hilado's formal unpacking of
initial theta data, last revised 19 June 2025:
https://arxiv.org/abs/2004.13228

Kirti Joshi has an independent Arithmetic Teichmuller Spaces program claiming a
Rosetta-stone route and a proof of Corollary 3.12; this should be tracked as a
related but separate line rather than imported as an assumption:
https://arxiv.org/abs/2401.13508

## Formalization Strategy

The project should proceed from explicit interfaces toward mathematical content.
For this domain, premature deep definitions are risky: if a Lean structure hides
one of the contested identifications, it can accidentally assume the conclusion.

Initial milestones:

1. Build a vocabulary layer for species, mutations, labeled copies, forgetful
   maps, and full poly-isomorphism-like data.
2. Formalize a small "real line copy" discipline: what it means to compare
   q-side and Theta-side log-volumes, which identifications are used, and which
   diagrams commute.
3. Encode the Stage 1 target as an interface: the hypotheses corresponding to
   "Theorem 3.11.5" plus simultaneous holomorphic expressibility and input
   prime-strip link properties should imply the Corollary 3.12 inequality.
4. Build countermodel tests for weakened hypotheses. These are as important as
   proofs, because they tell us which hidden identifications or indeterminacy
   bounds are mathematically doing work.
5. Expand backward into the first three triangles of Mochizuki's April 2026
   decomposition: descent, algorithmic parallel transport, hull+det, and the
   multiradial representation.
6. Only after the Stage 1 interface is stable, start importing serious Mathlib
   geometry and algebra for elliptic curves, valuations, monoids, Galois actions,
   Frobenioid-like categories, and anabelian reconstruction.

## Current Audit

As of 29 May 2026, the strongest Lean result is a conditional Stage 1 corridor,
not a proof of IUT III, Corollary 3.12 from Mochizuki's published hypotheses.
The final ordered-real calculation is formalized: from `qSigned <= thetaSigned`,
`0 < -qSigned`, and `thetaSigned <= C_Theta * (-qSigned)`, Lean proves
`-1 <= C_Theta`, strictness when `qSigned < thetaSigned`, and equality of the
signed readings in the boundary case `C_Theta = -1`.

The source-facing route is also formalized at the interface level. A
nonarchimedean `(Ind3)` entry, factored square/full-label SHE preservation, and
Hodge-descent packet transport compose to the final weighted-theta comparison.
With the displayed `C_Theta` bound, this route reaches the signed `C_Theta`
endpoint and packages the boundary-vs-strict dichotomy:

```lean
qSigned = thetaSigned ∧ thetaSigned < 0 ∨ (-1 : Real) < C_Theta
```

The factored square/full-label SHE preservation package no longer has to be
primitive in the finite Gaussian case: Gaussian degree evaluations with preserved
environment degree now construct that package and feed it directly into the
nonarchimedean `C_Theta` dichotomy. In the identity-coordinate Gaussian route,
equality at the canonical full label `1` supplies the required environment-degree
preservation, so that preservation is no longer an independent input there.
The raw nonarchimedean `(Ind3)` alignment is now also available through a
source-facing nonarchimedean upper-semi object equipped with 1-column q-pilot
log-Kummer data. The upper-semi inequality is still the Step (x) input; the
q-pilot column and log-Kummer non-interference are recorded before converting
to the raw real equalities used by the route. The active route does not use
equality of possible-image regions across `(Ind3)` as its Step (x) input.
Its source-side equality can already be
derived from the finite Kummer-plus-forgetting tensor-packet chain:
`holomorphicF -> holomorphicD -> monoAnalyticD`, where both steps preserve
product log-volume. The strongest route also no longer takes the direct
theta-to-entry-target equality; it derives that equality from a target-side
Step (x) alignment plus calibration of the local entry target with the
upper-semi target value. That target-side alignment can now be derived from
packet-normalized theta-source equality plus calibration of the upper-semi
target with the same packet-normalized value. The local entry target can also
be calibrated against this packet-normalized value, deriving equality with the
upper-semi target.

This is deliberately not marked as settling the dispute. The experiment report
keeps `disputeSettledByCurrentStage = false`. The remaining issue is whether the
records consumed by the later analytic route are constructible beyond the
legacy degree-level Hodge-theater, Hodge--Arakelov, and finite Theorem 3.11 toy models:
full Frobenioids, holomorphic hulls, determinants, and their local-field/Haar
compatibilities.

The latest source reread gives the following interpretation:

* IUT I supplies initial theta data and Hodge theaters. The code now represents
  the Definition 3.1 mod-`l` kernel/image and q-order conditions explicitly and
  derives typed `0`/`1` histories, owned prime strips, bridges, and
  `Theta^{+-ell-NF}` gluing from `InitialThetaData`. M2 also constructs the
  effective-divisor degree preorder categories and the typed theta-link/gluing
  equivalences. This is a degree-level categorical model, not the full
  Frobenioid/Kummer theory.
* IUT II supplies Hodge-Arakelov theta evaluation, Gaussian Frobenioids,
  conjugate synchronization, and multiradial/coric behavior. M2 canonically
  constructs the bad-place q-order and `q^(j^2)` pilots, actual quotient-torsor
  coordinates, `ZMod l` labels, sign classes, balanced-square weights, and
  normalized orbit averages from `InitialThetaData`. These remain
  finite-label/Gaussian-degree models, not the full theory.
* The legacy model associated with IUT III, Theorem 3.11 and Step (x), has a
  finite construction from the numerical pilots: a typed procession, `ZMod l`
  `(Ind1)/(Ind2)` actions and generated quotient, directed `(Ind3)` lifts,
  nonempty possible images, a vertical log-Kummer bijection from the bad-local
  quotient torsor, and finite transport laws named IPL/SHE/APT. These are not
  the paper's processions, indeterminacies, log-Kummer correspondence, or
  algorithms. Step (xi) is represented by conditional hull/log-volume and
  analytic descent records. Step (xii) is represented by a local Frobenioid
  shift quotient experiment.
  A separate source layer now contains an actual `Z x Z` family of distinct
  Hodge theaters carried by F-theta bridges. Adjacent vertical coricity is
  inverted and composed to obtain one fixed `n,circle` bridge and comparison
  from every `m`. Ind1 is derived from a functor on processions; Ind2's
  direct-sum, tensor, and full local-family actions are derived from independent
  summand actions. The source layer also has a complete unquotiented
  multiradial presentation, its exact Ind1/Ind2 quotient, a source-shaped Ind3
  common-container interface, and four distinct horizontal compatibility
  interfaces. It is still not a construction of Theorem 3.11: the presentation,
  vertical Kummer/Ind3 data, and horizontal squares are not yet constructed
  from the lattice and the preceding IUT I-II results.
* IUT IV is represented only as conditional ordered-real and elementary
  estimate algebra downstream of a Corollary-3.12-shaped input.
* The Scholze-Stix concern is addressed only at the diagnostic level: Lean keeps
  the `j^2` representative level, sign quotient, averages, ordered real-line
  transports, and hull/log-volume endpoint as separate types. It proves that a
  balanced sign-compatible level alone is not enough for the final route.

The tracked paper draft `paper/IUT_FORMALIZATION_3_12_DRAFT.tex` is the concise
mathematical state document. The old formalization-note markdown files are not
part of the current workflow.

## Lean Layout

This is a Lean 4.30.0 project with Mathlib.

Current modules:

* `Iut.Basic`: root import for the current Stage 1 corridor.
* `Iut.Foundations.Species`: minimal species/mutation and labeled-copy
  bookkeeping.
* `Iut.Foundations.RealLineCopy`: explicit labeled real-line copies and
  positive-scale transports.
* `Iut.Foundations.TransportDiagram`: coherent parallel transport diagrams and
  the scalar insertion obstruction.
* `Iut.Foundations.IndeterminacyRelation`: region-valued comparison interface
  separating exact equality from indeterminacy membership.
* `Iut.Foundations.RegionMeasure`: abstract monotone real-valued measures for
  log-volume-shaped estimates.
* `Iut.Foundations.CommonTargetBound`: measured common-target packages for
  comparison families, modeling the post-hull upper-bound interface.
* `Iut.Foundations.TransportedRegionFamily`: comparison-family presentation with
  explicit choice-dependent transports and target regions.
* `Iut.Foundations.QualitativeData`: structured inert IPL/SHE/APT data records,
  typed identifiers, and relation records for qualitative bookkeeping.
* `Iut.Foundations.Orbicurve`: source-facing etale stacks over `Spec(F)`,
  actual strong-transformation morphisms, canonical orbifold signatures stored
  on the represented stacks and exposed by signature-unique
  hyperbolic-geometry certificates,
  coherent sign actions as pseudofunctors, sign-invariant morphisms with the
  `C2` cocycle, and the bicategorical quotient universal property via
  factorization and full faithfulness on 2-cells,
  Galois-category-certified profinite fundamental groups, open embeddings, and
  exact profinite fundamental-group sequences.
* `Iut.Foundations.OrbicurvePullback`: actual restriction of scalars
  `Sch/K -> Sch/F`, scalar extension of etale stacks and orbicurves by
  pseudofunctor equivalence, scalar extension of morphisms with component and
  naturality comparison, 2-commutative squares, pseudo-cones, and the full
  two-pullback universal property through compatible 2-cell lifting and faithfulness.
* `Iut.Foundations.EtaleThetaQuotient`: lower-central theta quotients,
  the descended elliptic quotient and theta center, rank-one/rank-two
  realization data, continuous profinite Lagrangian `Z/lZ` quotients with
  derived open kernels, and nonzero labels modulo sign.
* `Iut.Foundations.EtaleThetaCovers`: linked geometric/arithmetic/Galois and
  cuspidal exact sequences, distinct class-two theta and rank-two elliptic
  arithmetic quotients, the type-`(1,l-torsion)` Lagrangian quotient on the
  latter, Proposition 2.2's direct-product inversion eigenspaces with actual
  conjugation compatibility, and the theta-root subgroup derived as the
  preimage of a chosen Galois splitting. The theta-root realization records
  the normalizing order-two lift, unique admissible coset, conjugation, and
  generation data of Proposition 2.2(iii); the module also constructs the
  profinite Tate direction and continuous reduction used by bad-place
  standard-type factorizations, their cuspidal sign-compatible splitting, and
  the canonical sign orbit of `1 mod l`.
* `Iut.Foundations.SourceInitialThetaData`: the replacement path for
  Definition 3.1, constructing the punctured curve from the affine coordinate
  ring of its stored Weierstrass equation, identifying it with the complement
  of the closed origin section in the chosen compactification, classifying
  stable and multiplicative reduction on local minimal equations independently
  of the stored presentation, and giving a bicategorical equivalence to its
  representable Yoneda-style etale
  pseudofunctor and a coherent sign
  action identified with the coordinate-induced involutive scheme morphism,
  stack morphisms,
  certified fundamental groups, exact
  profinite sequences, compatible open immersions, a field-of-moduli witness
  identified inside the selected `Fbar` with the fixed field of its
  geometric-`j` stabilizer, the maximal solvable extension in the same `Fbar`
  as the compositum of finite solvable Galois layers, and
  the mod-`l` kernel field as an equality of intermediate fields,
  the induced arithmetic theta and elliptic quotients over the scalar-extended
  `K`-core, cuspidal and Lagrangian quotients, inversion splitting,
  theta-root subgroup, explicit
  type-`(1,l-torsion)` cover/sign-quotient stacks constrained by the derived
  open cover group, and global plus bad-local theta-root/sign-quotient stacks
  with their derived arithmetic groups and open-subgroup chains. The place
  projections are canonical restrictions and local core diagrams are supplied
  at every `K`-place, with decomposition subgroups characterized as stabilizers
  of actual prolongations to `Kbar`; every selected completion carries a scalar extension of
  the type-`(1,l-torsion)` cover,
  compatible local-to-global fundamental groups and elliptic quotient, and a
  complete transported cusp atlas represented by cuspidal decomposition exact
  sequences. The IUT I, Definition 1.1 dependency is explicit: discarded
  inertia defines `Delta dagger`, its eigenspaces define continuous
  `J_X/J_C` quotients, the doubled-cusp section has a proved normal image, and
  the arrowed-cover subgroups are its source-prescribed preimages. At good
  finite places this entire construction and both arrowed stacks commute with
  scalar extension. The selected sign label is derived from a sheet
  representative; localization preserves it, and bad-place canonicity is
  proved. It also contains absolute
  Galois/decomposition-subgroup diagrams, plus Tate parameters with
  valuation-derived prime-to-`l` orders and geometric uniformizations at every
  `F`-place above the bad moduli locus and at selected bad `K`-places. These
  stack, compactification, and boundary-atlas
  realizations are interfaces; their construction from compactified
  finite-etale covers remains open.
* `Iut.Foundations.SourceFrobenioidBirationalization`: the arbitrary-
  Frobenioid part of Frobenioids I, Proposition 4.4 currently justified by the
  generic axioms: co-angular-pre-step localization, the filtered Hom-colimit
  comparison using the derived Proposition 1.11(vii) square, faithful
  localization, and the `C -> F_(Phi^gp) -> F_(0_D)` diagram. The general
  target Frobenioid axioms, rational-function transport, `Phi^birat` exact
  sequence, and clause-(iv) dictionary remain open; the complete existing
  result is specific to the Theorem 5.2 model.
* `Iut.SourceTrace.M1M3PaperLedger`: exact IUT I-III and transitive Etale Theta
  PDF hashes and a checked 130-clause source-to-Lean status matrix, including
  21 clauses that currently pass their clause-level source audits.
* `Iut.SourceTrace.IUTIVPaperLedger`: exact IUT IV PDF hash and a separate
  checked 19-clause ownership/status matrix for the public IUT IV surface. It
  distinguishes exact algebra from conditional shadows and currently makes no
  source-faithful IUT IV claim.
* `Iut.Foundations.AlgorithmicOutput`: opaque IPL/SHE/APT qualitative-property
  interface for transported algorithmic outputs.
* `Iut.Foundations.AlgorithmicBridge`: explicit bridge schemas from certified
  or structured qualitative output to measured common-target-bound data,
  including named hull+det, HDD, HDD-after-SHE, common-container, and
  real-comparison-chart bridge slots plus chosen outputs, charted q-values,
  memberships, target volumes, and Theta bounds.
* `Iut.Stage1.PilotComparison`: neutral endpoint package for the Corollary
  3.12 target shape; its projection theorem only unpacks an already supplied
  endpoint comparison.
* `Iut.Stage1.CorollarySchema`: signed-real schema for producing the
  Corollary-3.12-shaped pilot inequality from bridge output.
* `Iut.Stage1.SourceObligations`: source-obligation ledger for the structured
  Stage 1 final comparison, now requiring a charted common-container bridge and
  chosen output with charted q/membership/target/Theta values; the stored
  Theta common bound is tied to `chartedContainer.apply certificate`.
* `Iut.Stage1.IUTSourceScaffold`: non-toy provider scaffold whose public Stage
  1 endpoints are obtained only from a completed source-obligation ledger.
* `Iut.Stage1.IUTStage1Data`: pre-ledger data layer for future IUT-specific
  Stage 1 constructions, with explicit promotion obligations before the public
  endpoint is available.
* `Iut.Stage1.IUTStage1ConstructedTheorem311`: explicitly legacy finite model
  of translations, quotients, a preorder, and finite-coordinate transport; it
  does not discharge Theorem 3.11.
* `Iut.Stage1.IUTStage1SourceCore`: source-facing labels, package records,
  indeterminacy bookkeeping, finite local log-volume objects, and the initial
  Remark 3.12.2 corridor.
* `Iut.Stage1.IUTStage1Source`: continuation of the source-facing package for
  the Theorem 3.11 to Corollary 3.12 boundary, including the hull, Gaussian,
  transport, and endpoint route obligations.
* `Iut.Stage1.IUTStage1Experiments`: finite-model tests and theorem exports for
  the current Corollary 3.12 corridor, including the label, Gaussian,
  affine-action, and pointwise/aggregate separation results.

Useful commands:

```bash
lake build
pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory=paper paper/IUT_FORMALIZATION_3_12_DRAFT.tex
lake exe cache get
```

## Apodeixis

The sibling repository `../Apodeixis` is a Rust-based collaboration and
continuous-verification platform for formal mathematics. Its current Lean path
expects repositories to build with commands such as `lake build`, and its longer
term runtime design supports Lean goal-state and tactic operations through a
process-adapter backend. This repository should stay conventional as a Lake
project so it can later be ingested by Apodeixis without custom handling.

## TODO

Near-term engineering:

* Split `Iut/Stage1/IUTStage1Source.lean` into reviewable modules for finite
  labels/Gaussian data, Step (xi) hull and determinant endpoints, Step (xii)
  Frobenioid shifts, and IUT IV ordered-real algebra.
* Keep theorem names stable while refactoring; rebuild after each mechanical
  move.
* Add more experiment exports for any new source-derived route theorem, so the
  report surface tracks which assumptions have been eliminated.

Near-term mathematics:

* Extend the Gaussian-derived factored SHE construction beyond finite
  degree-evaluation and canonical-label shadows toward actual Gaussian/Frobenioid
  material corresponding to IUT II.
* Replace the current hull/determinant obligation records with formal
  holomorphic-hull and determinant operations from IUT III, Remark 3.9.5 and
  Step (xi).
* Extend the constructed finite IPL/SHE/APT compatibility through the analytic
  Step (xi) common-container and hull/determinant layers.
* Continue testing weakened hypotheses to identify exactly which comparison
  level or preservation property is mathematically necessary.

Longer-term mathematics:

* Refine the degree-level Frobenioid realization with the richer categorical,
  divisor, and Kummer structures required by later source arguments.
* Enrich the finite vertical log-Kummer correspondence with the local-field,
  log-shell, and Haar structures required by the analytic Step (xi) route.
* Connect the conditional IUT IV ordered-real estimates to actual arithmetic
  height, log-different, log-conductor, and bounded-discrepancy statements.
