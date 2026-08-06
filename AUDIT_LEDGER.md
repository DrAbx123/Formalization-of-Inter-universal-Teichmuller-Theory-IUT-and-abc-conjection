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
| `IUTI/InitialTheta`, `IUTI/HodgeTheater`, `IUTII/Frobenioid`, `IUTII/Kummer` | **mixed: 50 proved units / 6 interface / 4 pending source obligations** | The project now contains real arithmetic, the Frobenioids I Theorem 5.2 model category, its Proposition 4.4 Hom-colimit birationalization and `O^times ~= B` naturality, the objectwise zero-divisor `O^triangle`/effective-rational-function equivalence, the finite-place MLF integral monoid and its sequential ind-topological reconstruction, the full Proposition 2.2 `D*` functor, generic universal-pro-object evaluation, torsion-cyclotomic and Kummer kernels, theta quotients, and prime-strip kernels. It still does not construct the paper's actual MLF/CAF Frobenioid and identify its categorical evaluation with the reconstructed local integral carrier, or construct complete initial theta data, Hodge theaters, theta-links, and log-links. The four source-specific obligations remain pending; work-weighted C-layer completion is conservatively approximately 59--61%, not the ratio of compiled files. |
| `IUTII/Frobenioid/PrimeStripArithmetic` | **proved arithmetic kernel** | Finite interval prime-index set, primality projection, and interval monotonicity are proved with Mathlib's finite-order API; this is not an IUT Frobenioid prime strip. |
| `IUTII/Frobenioid/PrimeStripDegree` | **proved arithmetic kernel** | A finite family of ordinary commutative value monoids with official `MonoidHom` degree maps into `Multiplicative ℝ`; local multiplication and finite global degree additivity are proved. The data are not claimed to be an etale/Frobenioid realization. |
| `IUTI/HodgeTheater/PrimeStripCore` | **proved source-data kernel / realization pending** | `DPrimeStrip` and `FPrimeStrip` use Mathlib groups, surjective `MonoidHom`s, `Subgroup.ker`, `MulAut` actions, and the proved degree kernel. Forgetful maps, geometric kernels, action laws, and global degree laws compile and are axiom-audited; no arithmetic-geometric existence theorem is asserted. |
| `IUTI/HodgeTheater/HodgeTheaterCore` | **interface with proved link algebra** | A source-facing theater carries explicit initial arithmetic data, a concrete F-prime-strip carrier, and a finite theta packet. Prime-strip equivalence, theta-q/scale alignment, symmetry, composition, and three-theater source-to-target transport are proved. Existence of the paper's theaters, histories, anabelian reconstruction, and Hodge-Arakelov compatibility remain pending. |
| `IUTI/HodgeTheater/LocalPrimePlaces` | **proved local carrier kernel / realization pending** | Rational-prime labels, finite prime-interval labels, `ℚ_[p]`, algebraic-closure absolute Galois groups, the induced action on local units, and a nontrivial local q-parameter use Mathlib definitions. The projection is intentionally the identity because the etale fundamental-group quotient is not yet constructed. |
| `IUTII/Kummer/TimesMuQuotient` | **proved algebraic quotient/action kernel / IUT identification pending** | For an actual commutative unit group, the quotient by the full torsion subgroup, its canonical map and kernel, descended automorphism action, equivariance, action laws, and torsion-freeness are proved. The `FPrimeStrip` bridge uses the canonical unit group `(F.Mon v)ˣ`; no ind-topology or group/Frobenioid Kummer comparison is asserted. |
| `IUTII/Kummer/TimesMuIsm` | **proved conditional Ism/orbit kernel / representative existence pending** | Open-subgroup fixed units, invariant images modulo torsion, the exact equivariant/image-preserving Ism subgroup, compatible isomorphisms, their Ism action, and uniqueness of the resulting orbit are constructed and proved. Lean constructs the identity representative for one action but does not assert that the paper's distinct group-theoretic and Frobenioid actions admit a compatible representative. |
| `IUTII/Kummer/LocalFieldRigidity` | **proved local-field `G_m` rigidity / broader Kummer faithfulness pending** | Residual-finiteness root rigidity, profiniteness of valuation-ring units, triviality of a local-field unit with roots of every positive degree, and injectivity from the standard multiplicative Kummer-kernel characterization are proved. Arbitrary-torus and semi-abelian Kummer faithfulness are not claimed. |
| `Iut/Foundations/ContinuousH1` | **proved continuous-cohomology kernel** | Continuous nonabelian `H^1`, restriction, open-subgroup germ representatives, coboundary equivalence, and the abelian germ group laws are constructed. This is an exact upstream port except for removal of one unused broad import; it does not supply an IUT arithmetic action. |
| `IUTII/Kummer/RationalRootSystem` | **proved compatible-root kernel** | A single compatible rational-power homomorphism is obtained by extending `Z -> B` across `Z -> Q` using injectivity of divisible abelian groups. Algebraically closed field units instantiate it; unrelated choices for each degree are not used. |
| `IUTII/Kummer/ContinuousKummerGerm` | **proved one-unit continuous Kummer germ / global and Frobenioid comparison pending** | For an open-subgroup-fixed unit, compatible rational roots produce a continuous crossed homomorphism into the genuine cyclotome `Hom(Q/Z,B)`, a local continuous `H^1` class, and a germ. Changing the root system is proved to be an explicit coboundary. A homomorphism on all units, local absolute Galois continuity, Frobenioid evaluation, and the group/Frobenioid comparison remain pending. |
| `IUTII/Kummer/CanonicalKummerMap` | **proved group-side Kummer homomorphism / local arithmetic instantiation pending** | Every element of a divisible commutative discrete coefficient group has an open stabilizer. On intersections of stabilizers, product root systems prove the germ multiplication law, and the canonical map `B ->* H1_germ` is constructed. The local absolute Galois action, Frobenioid evaluation, and the Definition 4.9 group/Frobenioid comparison remain pending. |
| `IUTII/Kummer/LocalGaloisKummerAction` | **proved discrete local Galois action / ind-topological and Frobenioid realization pending** | For `Gal(Qbar_p/Q_p)` with its Krull topology and an explicitly declared discrete topology on algebraic-closure units, the unit stabilizer is identified with the field stabilizer and proved open from integrality. This yields a genuine continuous action and local group-side Kummer homomorphism. It is not the source's ind-topological integral monoid or Frobenioid evaluation. |
| `IUTII/Frobenioid/LocalTorsionCyclotome` | **proved local torsion-cyclotomic/rootability construction** | Lean proves the multiplicative rational circle `Q/Z` equivalent to all roots of unity in an algebraic closure of a characteristic-zero field, composes this with the proved integral-unit torsion equivalence, and transports algebraic-closure divisibility to `RootableBy Nat` on the actual local Grothendieck groupification. No cyclotomic structure is accepted as a field or premise. |
| `IUTII/Frobenioid/LocalMLFTMPair` | **proved canonical mono-analytic MLF `TM` model / Frobenioid comparison pending** | The acting group is the actual Krull-topological `Gal(Qbar_p/Q_p)`, the augmentation is the continuous identity surjection, and the arithmetic monoid/action are the proved local integral model. Pullbacks of genuine Krull-open stabilizers are proved to fix their elements. Unit and `times-mu` actions feed the existing Ism kernel, but no distinct group/Frobenioid comparison is asserted. |
| `IUTII/Frobenioid/LocalGroupificationAction` | **proved discrete continuous groupification action** | The local integral-monoid action is extended through the Grothendieck-group universal property. Its stabilizer is pulled back from the genuine Krull-open stabilizer of the corresponding algebraic-closure unit. The unit embedding is proved injective and equivariant, and the groupification equivalence is proved equivariant with the actual algebraic-closure action. This is not a Frobenioid evaluation or the source's unit-valued Kummer comparison. |
| `IUTII/Frobenioid/LocalIntegralUnitKummer` | **proved integral-unit root realization / Frobenioid comparison pending** | Compatible rational roots in the actual local Grothendieck group are used to prove every Galois root ratio is torsion, lift it uniquely to an integral unit, and construct the resulting unit-valued `Q/Z` cyclotome, continuous crossed cocycle, and `H^1` germ. No Kummer comparison is assumed as data. |
| `IUTII/Frobenioid/LocalUnitKummerMap` | **proved canonical unit Kummer homomorphism / Frobenioid comparison pending** | Any two compatible-root choices are proved to differ by an explicit coboundary. Product root realizations prove multiplication of germs, yielding a genuine monoid homomorphism from local integral units. This still supplies only the group-side map. |
| `IUTII/Frobenioid/LocalUnitKummerInjectivity` | **proved mono-analytic injectivity / Definition 4.9 comparison pending** | A trivial germ yields roots of every positive degree fixed by one open subgroup. The fixed field is finite over `Q_p`; its integral-closure unit group is residually finite, using an explicit equivalence between the canonical valuation ring and `Z_p`. Hence the constructed mono-analytic integral-unit Kummer homomorphism is injective. Frobenioid-side evaluation and the group/Frobenioid comparison are not asserted. |
| `IUTII/Frobenioid/LocalMLFPrimeStripBridge` | **proved definitional compatibility / categorical Frobenioid evaluation pending** | The integral F-prime-strip value object was corrected from `(LocalIntegralMonoid p)^x` to `LocalIntegralMonoid p`, so the generic Kummer layer takes units exactly once. Its monoid, unit, and `times-mu` actions are then proved by `rfl` to be the canonical local MLF `TM` actions. This is not yet the universal-cover Frobenioid evaluation functor. |
| `IUTII/Frobenioid/LocalIntegralUnitEvaluationImage` | **proved exact arithmetic evaluation image / categorical-local identification pending** | The integral-unit evaluation has exactly the algebraic-closure units whose value and inverse are integral. The induced equivalence is proved compatible with the natural Galois action, descends through the full torsion quotient, and maps every open-subgroup invariant image exactly onto its counterpart, yielding a real carrier-level `Ism` orbit. The generic categorical `O^triangle(A)` now exists separately, but no theorem yet identifies it with this local carrier for an actual MLF Frobenioid or supplies the source's ind-topology. |
| `Iut/Foundations/SourceFrobenioidRationalMonoidTransport` | **proved restricted Frobenioids I Proposition 2.2(ii),(iv) transport kernel** | From the existing `FrobenioidPresentation.axioms`, Lean constructs contravariant pullback on the actual base-identity linear endomorphism monoids along linear arrows between isotropic objects, proves identity and composition on `(C^istr)^lin`, and constructs the injective isotropic-hull extension. The production file is byte-identical to `promachina/iut-lean@5e70fbe9`; no recognition/existence wrapper or new Frobenioid axiom is introduced. The extension to every arrow of `D*`/`D`, the universal-cover pro-object, and the IUT II Definition 4.9 evaluation remain separate obligations. |
| `Iut/Foundations/SourceFrobenioidIsotropicBase` | **proved Frobenioids I Proposition 2.2(i)** | Lean defines the paper's category `D*` with isotropic Frobenioid objects and base-category homs, then proves its tautological projection to `D` faithful and full. Essential surjectivity is constructed from Definition 1.3(i)(a) and an isotropic hull, yielding an actual `D* ≃ D`. The subsequent modules now extend `O^triangle` to all `D*` arrows and evaluate it on the standard pointed-Galois pro-presentation. |
| `Iut/Foundations/SourceFrobenioidCoAngularBaseChange` | **proved Proposition 2.2(ii) base-isomorphism transport** | From Definition 1.3(i)(b), isotropic hulls, and the proved Proposition 1.4/1.9 lemmas, Lean constructs an isotropic common midpoint with co-angular pre-steps over any prescribed base isomorphism. The resulting rational-monoid equivalence is proved independent of the common witness and satisfies identity, inverse, and composition laws; it is used by the completed arbitrary-base-arrow transport. |
| `Iut/Foundations/SourceFrobenioidBasePullbackLift` | **proved full Frobenioids I Proposition 2.2(ii) functor on `D*`** | Definition 1.3(i)(c) lifts every base arrow between isotropic objects to an actual pullback arrow after a source base isomorphism. Lean proves the lifted source isotropic, representative independence, source/target isomorphism naturality, the mixed pullback/pre-step squares, and identity and composition laws for arbitrary base arrows. These results package into the genuine contravariant functor `(D*)^op -> MonCat`; no recognition record or selected candidate is used. |
| `Iut/Foundations/SourceFrobenioidUniversalProEvaluation` | **proved generic IUT II Definition 4.9(i) categorical evaluation and action** | For a Galois structure and fiber functor on `D*`, Mathlib's pointed Galois objects give the cofiltered pro-representing system. Lean applies the proved `O^triangle` functor to the opposite system, takes its actual `MonCat` colimit, constructs the inverse-limit Galois action, and proves on every finite-level representative that the action is pullback along the inverse automorphism. An actual MLF/CAF Frobenioid, its Galois-category instance, the comparison with `LocalIntegralMonoid`, and the ind-topology remain pending. |
| `Iut/Foundations/SourceModelFrobenioid*` | **proved Frobenioids I Theorem 5.2 model chain** | The seven-file chain constructs the model category, divisor order, factorization and uniqueness, pre-step factorization, every Definition 1.3 axiom group, and the final `FrobenioidPresentation`. The input supplies only the rational-function additive group, divisor homomorphism, and naturality; the Frobenioid conclusion is not an input field. Six files are byte-identical to the fixed public snapshot and one has two explicit Lean 4.32.2 object annotations. |
| `SourceFrobenioidModelType`, `SourceModelFrobenioidBirational*`, `SourceModelFrobenioidColimit*`, and `SourceModelFrobenioidRationalNaturality` | **proved Frobenioids I Proposition 4.4/Theorem 5.2 birational chain** | The actual filtered Hom-colimit, fully faithful comparison with the concrete birational model, seven Definition 1.3 axiom groups, full Frobenioid presentation, rational-function natural isomorphism, unit restriction, and `DivB` compatibility are constructed. Eight files are content-identical to `promachina/iut-lean@0d52e0fd` after end-of-line normalization. The other three contain only Lean 4.32.2/linter migrations: unused simp arguments removed, Prop-valued `def`s changed to `theorem`s, and one explicit projection `change`; the propositions, hypotheses, and proof arguments are unchanged. This identifies the group-like birational `O^times`, not the integral monoid of IUT II Definition 4.9. |
| `Iut/Foundations/SourceModelFrobenioidZeroEvaluation` | **proved objectwise integral evaluation kernel / finite-stage comparison proved separately** | At the zero-divisor object of the actual model Frobenioid, Lean constructs a multiplicative equivalence between `O^triangle` and rational functions whose divisor lies in the effective monoid. Surjectivity is obtained from an explicit model arrow satisfying the original balance equation; no supplied recognition or existence field is used. Finite-stage divisor-effectivity versus local valuation-integrality is now proved in `SourceFiniteStageValuationDivisor`; the actual finite-stage ramification transitions, filtered-colimit evaluation comparison, Galois action, ind-topology, groupification, and Kummer compatibility remain pending. |
| `Iut/Foundations/SourceModelFrobenioidIntegralNaturality` | **proved natural integral-evaluation comparison for every model base arrow** | The zero-divisor section is constructed as a functor. Its transported `O^triangle` monoids and the effective rational-function submonoids are contravariant functors on the full base category, and Lean constructs a natural isomorphism between them. Effectivity under pullback follows from the original divisor naturality and `gpPullback_of`; no transition or recognition field is added. Specializing this generic theorem to the finite Galois stages still requires their genuine ramification-weighted divisor pullbacks. |
| `Iut/Foundations/SourceFiniteStageDivisorTransition` | **proved genuine finite-stage value-group and divisor transition system** | For every finite-stage inclusion, Mathlib's `ValuativeExtension.mapValueGroupWithZero` is conjugated through the independently chosen `ValueGroupWithZero ≃*o ℤᵐ⁰` normalizations. The resulting additive `ℤ` map is proved strictly monotone, equal to multiplication by a positive ramification index, and natural for units; the induced `ℕ` divisor pullbacks are injective and satisfy identity/composition. No compatibility of noncanonical stage normalizations is assumed. |
| `Iut/Foundations/SourceFiniteStageModelFrobenioid` | **proved finite-stage model Frobenioid input** | The opposite finite-stage category carries a universe-correct sharp, integral, saturated divisor monoid (`ULift ℕ`), ramification-weighted pullbacks, and the additive group of nonzero stage elements. The model `Input` and its `divisor_natural` field are constructed and proved from the transition theorem and the Grothendieck-group pullback calculation. This is the actual finite-stage carrier/input; the categorical universal-pro evaluation and its identification with `O^triangle` remain pending. |
| `Iut/Foundations/SourceFiniteStageModelEvaluation` | **proved finite-stage `O^triangle` identification, naturality, and reconstructed ind-colimit** | For the zero-divisor object of the finite-stage model, the generic effective rational-function submonoid is proved equal to the normalized-valuation nonnegative submonoid. An explicit multiplicative equivalence identifies the model `O^triangle` zero-object endomorphisms with the actual nonzero integral stage monoid, and its effective-side map is proved natural for every genuine stage transition. The stage integral `MonCat` filtered colimit is constructed and proved multiplicatively equivalent to the exhaustive `IndIntegralMonoid`. The proof uses the genuine Grothendieck-group equivalence, valuation/integrality theorem, actual `stageIntegralTransition`, and Mathlib filtered representative relation; it does not assert the categorical MLF/CAF `O^triangle` realization. |
| `Iut/Foundations/SourceMLFIntegralMonoid` and `IUTII/Frobenioid/MLFIntegralMonoidComparison` | **proved arithmetic monoid, groupification, and local comparison** | For an actual valued field, Lean uses the integral closure in its algebraic closure, removes zero, constructs the absolute Galois action, proves the fraction-field property, and identifies the Grothendieck group with algebraic-closure units. The existing `LocalIntegralMonoid p` is proved equivalent, including inclusion, groupification, and Galois action. This is an arithmetic carrier comparison, not yet a Frobenioid evaluation comparison. |
| `Iut/Foundations/SourceFinitePlaceMLFBase` | **proved finite-place local-field base / packaging only for the ind-colimit record** | The actual completion map `Q_p -> K_v`, continuity, scalar tower, finite dimensionality, nontrivial norm, characteristic zero, valuative relation, second countability, and rational local compactness are constructed from Mathlib and the existing finite-place extension theorem. `SourceFiniteIndTopologicalLocalModule` only packages a filtered topological-module cocone; existence for the required system is supplied by the following reconstruction, not assumed here. |
| `Iut/Foundations/SourceDefinition52LocalReconstruction` through `SourceDefinition52Sequential` | **proved IUT I Definition 5.2(v) finite-place reconstruction** | Finite Galois intermediate fields form the filtered stages; their module colimit is proved equivalent to the algebraic closure. Nonzero integral stage monoids exhaust the local integral monoid, transitions and the Krull action are continuous and equivariant, and a natural-number-indexed cofinal subsystem is constructed from countably many global-polynomial root witnesses. No candidate-existence record is used. The separate categorical identification with `O^triangle(A)` for an actual MLF/CAF Frobenioid remains pending. |
| `Iut/Foundations/SourceFiniteStageValuationDivisor` | **proved finite-stage valuation/divisor comparison** | Every finite Galois reconstruction stage is proved to be a nonarchimedean local field with value group `WithZero (Multiplicative Int)`. Lean constructs the normalized additive valuation, the genuine sharp saturated divisor monoid `Nat`, proves base-ring integrality iff the stage valuation is at most one by a minpoly/spectral-norm argument in both directions, and obtains a multiplicative equivalence between effective nonzero rational functions and `StageIntegralMonoid`. The stage integral monoid itself is not mislabeled as a sharp divisor monoid. |
| `Iut/Foundations/SourceTopologicalMonoidPresentation` | **data structure with proved morphism laws** | This is the exact minimal package extracted from the public Hodge-theater source: a monoid with topology and continuous multiplication, continuous monoid homomorphisms, composition, identity, and extensionality. It proves the packaging laws but asserts no IUT object existence. |
| `IUTII/Theta/FiniteThetaPacket` | **proved concrete lower packet / IUT identification pending** | A finite interval subtype supplies the standard Mathlib `Fintype`; the Gaussian packet is positive, nonzero, sign-symmetric, and has a proved finite log-volume identity. This is a lower numerical packet, not yet the paper's etale theta or Hodge-Arakelov object. |
| `IUTII/Theta/EtaleThetaQuotient` | **proved algebraic lower-central kernel / geometric realization pending** | The lower-central theta quotient, elliptic abelianization, exponent-`l` power quotients, canonical surjections, and central theta kernel are constructed with Mathlib commutator/normal-closure/QuotientGroup APIs. Profinite closedness, etale fundamental groups, and the rank-two arithmetic identification remain explicit obligations. |
| `IUTIII/Theorem311/*` | **claim only / interface vocabulary, with a proved generic kernel** | Theorem 3.11 output and Ind1--3 are tracked as obligations, not derived from number-field or elliptic-curve data. `Indeterminacy/QuotientTransport` proves representative-independent transport for arbitrary Setoids, but supplies no IUT-specific carriers or relations. |
| `IUTIII/Theorem311/Indeterminacy/OrbitTransport` | **proved group-action kernel** | Equivariant maps descend through Mathlib's official `MulAction.orbitRel` quotient, and a three-layer orbit transport has a representative formula. This is the Ind1/Ind2 mechanism, not the IUT-specific Galois/Kummer construction. |
| `IUTIII/Theorem311/Indeterminacy/UpperSemi` | **proved order kernel** | Set-valued upper-semi correspondences, singleton monotone maps, and composition are proved over standard preorders; this captures the logical direction of Ind3 without supplying the paper's log-Kummer correspondence. |
| `Iut/Foundations/SourceTemperedDeck*` | **proved tempered-deck kernel / arithmetic realization pending** | The literal deck groups, refinement transitions, locally-surjective universal-tree lifting, finite bounded lift fibers, cofiltered compatible sections, and every raw/literal deck projection are constructed and proved. The chain has no `sorryAx`; it does not construct stable reduction, Andre exactness, an arithmetic tempered tower, IPL/SHE/APT, or the Theorem 3.11 output. |
| `Iut/Foundations/SourceTemperedGaloisSplitter` through `SourceTemperedGeometricDomination` | **proved alternative construction kernel / paper-object identity pending** | Lean constructs a pointed Galois splitter, local component maps, universal sheet lift, corrected target points, branch naturality, and a literal domination morphism. These declarations are usable proved mathematics with no `sorryAx`. Their proof architecture targets *Semi-graphs of Anabelioids*, Proposition 3.6(ii), but exact definition-by-definition identity or a proved equivalence with every paper object has not yet been audited; they are not counted as IUT III Theorem 3.11, Ind1--3, IPL/SHE/APT, or Corollary 3.12. |
| `Iut/Foundations/SourceTemperedActionFactorization` through `SourceTemperedActionCoverEquivalence` | **proved 26-module action-cover classification kernel / paper-object identity pending** | The fixed `promachina@c7c06e23` chain constructs orbit factorization, component families, literal tempered covers, finite and componentwise associated quotients, normalized universal-cover refinements, the action-cover functor, and its full/faithful instances. All 26 modules compile with zero diagnostics and the sampled endpoints have no `sorryAx`. Thirteen files are byte-identical and thirteen contain only audited Lean 4.32.2 proof migrations. This remains a proposed construction of the *Semi-graphs of Anabelioids*, Proposition 3.6(ii), mechanism; exact definition-by-definition identity with the paper is pending, and none of IUT III Theorem 3.11, Ind1--3, IPL/SHE/APT, Corollary 3.12, or ABC is thereby proved. |
| `IUT_SUBTARGETS.md` | **research-target registry** | Separates proved Lean kernels, source-faithful IUT obligations, and external open-problem candidates; no candidate is counted as proved by the current project. |
| `IUTIII/Corollary312/StepXI/*` | **interface plus one marked `sorry`** | `cor312_of_constructed_stepXI` and the ordered corridor are proved from a supplied contract; `theorem311_produces_stepXI_contract` is the sole `sorryAx` reachable from the production entry point. `HolomorphicHull/Volume` additionally proves finite positive-packet determinant, tensor-product, rescaling, log-volume, and weighted-hull identities using the official `Matrix.det`, `Matrix.det_diagonal`, and `Finset` APIs. It does not construct the paper's holomorphic hull, local/global tensor normalization, or q-pilot objects. |
| `IUTIII/Corollary312/StepXI/FiniteCertificateBridge` | **interface** | `FiniteStepXILinkEvidence` makes `targetSigned`, IPL/SHE/APT evidence, and both comparison bounds explicit; from those supplied fields, Lean constructs a `StepXIContract` and proves the ordered conclusion. It does not prove any of the supplied source-facing fields. |
| `IUTIII/Corollary312/Routes` | **three claimed routes recorded / all pending** | The source-labelled Mochizuki 3.11.5 reorganization, Joshi's arithmetic-Teichmuller/Rosetta-Stone route, and Sarkisyan's explicitly claimed Erdos--Kac route are separate typed tags and audit obligations. No preprint result is imported as an axiom, and no route certificate is constructed. |
| `ABCBridge/Statement` | **proved statement layer** | `ABCConjecture` is the standard epsilon/constant radical proposition; the radical lemmas are checked against Mathlib. This is not a proof of the conjecture. |
| `ABCBridge/UnprovedTarget` | **pending metadata only** | The former unused `abc_conjecture_target := by sorry` declaration was removed. The file now records the unproved ABC target without creating a Lean theorem or a second `sorryAx`. |
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
| Ported public-foundation closure | **27/27 exit code 0; warning repaired** | The topology-ordered run is `logs/lean/serial-20260804-052013/summary.json`. Its sole diagnostics were two unused simp arguments in `SourceGluedFiniteEtaleTransition`; after removal, the complete affected upper closure passed with zero output in `logs/lean/serial-20260804-053109/summary.json`. |
| Refreshed countable-base kernels | **passed with zero output** | Exact `promachina@36ef280d` hunks for finite projection fibers, countable Galois levels, countable deck groups, and countable separators passed in `logs/lean/serial-20260804-054453/summary.json` and `logs/lean/serial-20260804-054422/summary.json`. |
| Ported foundation axiom sample | **passed** | `logs/lean/axioms-upstream-foundations-20260804-054745/axiom_audit.stdout.log`; all sampled declarations use only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. A full `Iut/Foundations` declaration scan reports zero top-level custom `axiom`/`opaque` declarations. |
| Final ported-foundation closure | **27/27, zero diagnostics** | `logs/lean/serial-20260804-055402/summary.json`; all 27 exit codes are 0 and all 54 stdout/stderr logs are empty after the countable-base port. |
| Temperoid and nested-quotient kernel closure | **5/5, zero diagnostics** | `logs/lean/serial-20260804-063139/summary.json`; connected finite coverings, kernel orbits, countable temperoids, the kernel-orbit/restriction adjunction, and nested normal quotients all compile, and all 10 stdout/stderr logs are empty. |
| Expanded public-foundation axiom sample | **passed** | `logs/lean/axioms-upstream-foundations-20260804-063457/axiom_audit.stdout.log`; the new quotient, continuity, connectedness, full-faithfulness, adjunction, and canonical-map injectivity samples use only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. |
| Mathlib 4.32.2 compatibility patch audit | **20/20 reverse checks passed** | `vendor/promachina/patches/4.32.2/MANIFEST.json`; the tracked closure now has 31 files, of which 20 are patched and 11 are byte-identical to the fixed source snapshot. |
| Tempered deck transition/projection closure | **3/3, zero diagnostics** | `logs/lean/serial-20260804-065656/summary.json`; the deck-group file is byte-identical to `promachina@c7c06e23`, while the transition and projection files contain only recorded Lean 4.32.2 normalization migrations. All six stdout/stderr logs are empty. |
| Tempered deck axiom sample | **passed** | `logs/lean/axioms-upstream-foundations-20260804-065850/axiom_audit.stdout.log`; ten samples from bounded lifts through the literal tempered projection use only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. |
| Tempered geometric-domination closure | **5/5, zero diagnostics** | `logs/lean/serial-20260804-080846/summary.json`; the Galois splitter, component map, universal sheet lift, target sheet lift, and geometric domination modules all compile, and all ten stdout/stderr logs are empty. |
| Tempered geometric-domination axiom sample | **passed** | `logs/lean/axioms-upstream-foundations-20260804-081211/axiom_audit.stdout.log`; nine splitter/lift/naturality/domination declarations use only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. |
| Tempered/action-cover construction closure | **26/26, zero diagnostics** | The first thirteen modules are covered by `logs/lean/serial-20260804-071152/summary.json`, `serial-20260804-072531`, `serial-20260804-073549`, `serial-20260804-074140`, and `serial-20260804-080846`; the final thirteen are in `logs/lean/serial-20260804-085836/summary.json`. All 26 exit codes are 0 and all 52 stdout/stderr logs are empty. |
| Tempered/action-cover endpoint axiom audit | **passed** | `logs/lean/axioms-upstream-foundations-20260804-090536/status.json`; finite-level full/faithful, connected/componentwise/global classification, refinement, geometric inverse-system, and action-cover full/faithful endpoints use only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. |
| Local integral-unit Kummer closure | **passed; zero diagnostics** | `logs/lean/local-unit-kummer-injectivity-20260805/lake-targets-zero-warning.log`; the root-choice-independent Kummer map and mono-analytic injectivity targets both build without warnings or errors. |
| Local integral-unit Kummer production and axiom audit | **passed** | `logs/lean/local-unit-kummer-injectivity-20260805/Project.log` and `axiom_audit.final.log`; all new sampled declarations use only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The custom declaration scan is in `custom_axioms.log` and reports zero top-level `axiom`/`opaque`. |
| Current aggregate after local integral-unit Kummer injectivity | **passed; zero diagnostics** | `logs/lean/local-unit-kummer-injectivity-20260805/LeanFormal.log`; `lake build LeanFormal` completed successfully (3738 jobs). The only production `sorryAx` remains `theorem311_produces_stepXI_contract`. |
| Frobenioid rational-monoid transport closure | **2/2 exit code 0; zero diagnostics** | `logs/lean/serial-20260805-033034/summary.json`; the byte-identical source module and production `Project.lean` both compile and all four stdout/stderr files are empty. |
| Frobenioid rational-monoid axiom audits | **passed** | `logs/lean/source-frobenioid-rational-monoid-transport-20260805/upstream_foundations_axiom_audit.stdout.log` and `axiom_audit.stdout.log`; the new transport endpoint uses only `propext`, `Classical.choice`, and `Quot.sound`. The only production `sorryAx` remains `theorem311_produces_stepXI_contract`. |
| Current aggregates after rational-monoid transport | **passed; zero diagnostics** | `logs/lean/source-frobenioid-rational-monoid-transport-20260805/Project.build.stdout.log` reports 3740 jobs and `LeanFormal.build.stdout.log` reports 3742 jobs. Both stderr logs are empty; the combined warning/error scan has zero matches. |
| Frobenioid isotropic-base `D*` closure | **2/2 exit code 0; zero diagnostics** | `logs/lean/serial-20260805-034535/summary.json`; `SourceFrobenioidIsotropicBase.lean` and `Project.lean` compile with four empty stdout/stderr logs. The axiom audits are under `logs/lean/source-frobenioid-isotropic-base-20260805/` and report only `propext`, `Classical.choice`, and `Quot.sound`. Aggregate builds complete at 3741 and 3743 jobs. |
| Frobenioid co-angular base-change closure | **2/2 exit code 0; zero final diagnostics** | `logs/lean/serial-20260805-035654/summary.json`; the new module and `Project.lean` have empty diagnostics. The final standalone logs are `logs/lean/source-frobenioid-coangular-base-change-20260805/module.final.*.log`; earlier `attempt-*` logs retain the ordinary elaboration errors repaired during development and are not final build results. Both axiom audits pass, and aggregate builds complete at 3742 and 3744 jobs. |
| Frobenioid base-arrow lift and representative-independence closure | **passed; zero production diagnostics** | `logs/lean/serial-20260805-044224/summary.json` records exit code 0 and empty stdout/stderr for `SourceFrobenioidCoAngularBaseChange.lean`, `SourceFrobenioidBasePullbackLift.lean`, and `Project.lean`; the general production audit also passes. The corrected foundations audit is `logs/lean/serial-20260805-044431/summary.json`. All sampled new endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`; the source scan finds no top-level `axiom`, `opaque`, or `sorry`. The sole project `sorryAx` remains `theorem311_produces_stepXI_contract`. |
| Full `D*` rational-monoid functor and universal-pro evaluation closure | **5/5 exit code 0; zero diagnostics** | `logs/lean/serial-20260805-051841/summary.json` covers the completed base-arrow module, universal-pro evaluation module, production entry point, and both axiom audits. The arbitrary-arrow composition law, `(D*)^op -> MonCat` functor, inverse-limit Galois action, and finite-level action formula depend only on `propext`, `Classical.choice`, and `Quot.sound`; both new source files contain no direct `axiom`, `opaque`, or `sorry`. The only production `sorryAx` remains `theorem311_produces_stepXI_contract`. |
| Model Frobenioid and Definition 5.2 local reconstruction closure | **passed; zero diagnostics** | `logs/lean/definition52-local-reconstruction-closure-20260805/Project.stdout.log` records the production closure at 3803 jobs; the final finite-place base, local reconstruction, continuity, joint continuity, ind-system, and sequential module logs are under `logs/lean/source-*20260805*`. The production files contain no direct `axiom`, `opaque`, or `sorry`. |
| Definition 5.2 endpoint axiom audits | **passed** | `logs/lean/definition52-local-reconstruction-closure-20260805/upstream_foundations_axiom_audit.stdout.log` and `axiom_audit.stdout.log` show only `propext`, `Classical.choice`, and `Quot.sound` for the model Frobenioid, groupification, finite-stage reconstruction, continuity, ind-limit, sequential, and local-comparison endpoints. The only production `sorryAx` remains `theorem311_produces_stepXI_contract`; `custom_axioms.stdout.log` reports zero custom declarations. |
| Current aggregate after Definition 5.2 local reconstruction | **passed; zero diagnostics** | `logs/lean/definition52-local-reconstruction-closure-20260805/LeanFormal.stdout.log`; `lake build LeanFormal` completed successfully at 3805 jobs. Provenance and every source/production SHA-256 are recorded in `vendor/promachina/selective-port-model-frobenioid-definition52-0d52e0fd.json`. |
| Model birational/naturality/zero-evaluation closure | **passed; zero final diagnostics** | `logs/lean/model-zero-evaluation-closure-clean-20260805-071152/LeanFormal.stdout.log` records the warning-free 3817-job aggregate build. `logs/lean/serial-20260805-070308/summary.json` covers the zero-evaluation module, production `Project.lean`, and the first endpoint audits; the preceding final standalone logs are `serial-20260805-063307`, `063456`, `063515`, `063813`, and `063832`. All four sampled endpoints depend only on `propext`, `Classical.choice`, and `Quot.sound`; the twelve new files contain no direct `axiom`, `opaque`, or `sorry`. The sole project `sorryAx` remains `theorem311_produces_stepXI_contract`. Provenance is recorded in `vendor/promachina/selective-port-model-birational-zero-evaluation-0d52e0fd.json`. |
| Finite-stage valuation/divisor closure | **passed; zero diagnostics** | `logs/lean/finite-stage-integral-production-20260805-0850/SourceFiniteStageValuationDivisor.stdout.log` is empty with exit code 0. `logs/lean/finite-stage-integral-closure-20260805-0900/lake-build-targets.stdout.log` records successful 3817-job builds of the module and production entry point; both stderr logs are empty. The two axiom-audit logs in the same directory show only `propext`, `Classical.choice`, and `Quot.sound` for the integral/valuation comparison and effective-rational-function equivalence. The module contains no `sorry`, custom `axiom`, or `opaque`. |
| Model integral-evaluation naturality closure | **passed; zero diagnostics** | `logs/lean/model-integral-naturality-closure-20260805-1000/production.stdout.log` records successful 3818-job builds of the module and production entry point; all three stderr logs are empty. Both axiom audits show only `propext`, `Classical.choice`, and `Quot.sound` for `effectiveRationalFunctionPullback` and `zeroRationalFunctionNatIso`. The sole production `sorryAx` remains `theorem311_produces_stepXI_contract`. |

### Public repositories checked at fixed commits

| repository (commit) | build/scope actually observed | status at the IUT wall |
|---|---|---|
| [promachina/iut-lean](https://github.com/promachina/iut-lean) `4953e647` | 128 Lean files. The project has an extensive Stage-1 source-facing layer and its own dependency/audit documents. `AlgorithmicOutput` stores `ipl`, `she`, `apt` as `Prop` fields; downstream `CorollarySchema`/`SourceObligations` prove the ordered comparison once certificates, a common-target bound, hull/measure data, and q-positivity are supplied. | **interface**. The repository README explicitly lists full Frobenioids, holomorphic hulls, determinants, and local-field/Haar compatibility as remaining construction work. A passing downstream theorem is conditional on those records. |
| [promachina/iut-lean](https://github.com/promachina/iut-lean) `bbb736cd` (current HEAD checked 2026-08-04; local production snapshot starts at `0d52e0fd`) | 190 Lean files plus the Definition 3.1 finite-etale certification update. The latest commit adds generic open-subgroup/stabilizer constructions and strengthens sign/l-torsion/theta-root records with finite-etale and derived-fundamental-group certificates. Its `lakefile.toml` pins Mathlib `v4.30.0`, whereas this project uses Lean/Mathlib `4.32.2`. | **mixed**. The generic profinite open-subgroup and cover-fiber stabilizer constructions are real and reusable. The decisive finite-etale existence, source-group/stabilizer equivalences, and exact-sequence compatibility remain supplied structure fields; the update improves type discipline but does not construct Definition 3.1 geometry. Details are in `vendor/promachina/review-bbb736cd.json`. |
| [promachina/iut-lean](https://github.com/promachina/iut-lean) `2eb61e1b` (checked 2026-08-05) | 16 commits after `ea91200b`, 29 changed files/20 Lean files: Tate coefficients, local/global Frobenioid reconstruction packages, archimedean geometry, bad-place evaluation sections, and a D-theta bridge. The changed Lean tree has no top-level `axiom`, `opaque`, or explicit `sorry`. | **mixed, selective reuse only**. The derived section/decomposition-group, finite-branch, realified-ray, and categorical transport proofs are real. The analytic geometry, Andre splitting, reconstruction, and local/global Frobenioid existence are still prerequisite/reconstruction structure fields. The reusable torsion-cyclotome and groupification-rootability proof was specialized to our actual local monoid; wrappers were not bulk-ported. See `vendor/promachina/review-2eb61e1b.json`. |
| [promachina/iut-lean](https://github.com/promachina/iut-lean) `7bea5b03` (checked 2026-08-05) | Two substantive commits add 2835 foundation lines for Topics I chain reconstruction and IUT I Definition 5.2(v)-(viii) local coric reconstruction. The changed source has no top-level `axiom`, `opaque`, or explicit `sorry`. | **conditional reconstruction framework; no bulk port**. The comparison types and derived critical-predicate/unit-equivalence kernels are useful, but final objects are selected from `candidate_exists`, `candidates_isomorphic`, and `compatible_exists` recognition fields. Our new Kummer injectivity can later discharge one selected-place injectivity field only after the missing type bridge, Frobenioid embedding, and exact-image proof exist. See `vendor/promachina/review-7bea5b03.json`. |
| [promachina/iut-lean](https://github.com/promachina/iut-lean) `f87990b4` (checked 2026-08-05) | Merge PR 231 brings the previously reviewed `87d595c7` F-bridge branch into master. The master and reviewed branch tree hashes are identical, so there is no new content beyond that audit. | **no additional port**. The derived range/composition/associated-D kernels remain conditional on recognition-supplied pullbacks, global Frobenioids, local-to-global lifts, and theater isomorphisms. The directly reusable Proposition 2.2 rational-monoid transport was ported separately. See `vendor/promachina/review-f87990b4.json`. |
| [Takkun-kohinata/IUT_LEAN](https://github.com/Takkun-kohinata/IUT_LEAN) `9d56c46` (refreshed 2026-08-04; unchanged) | 68 Lean files. `Multiradial/Cor312.lean` proves its stated abstract corridor; `Diophantine/Szpiro.lean` defines the Szpiro-shaped conclusion but leaves its truth as `DiophantineMainTheorem`; `InitialThetaData/Deferred.lean` documents deferred geometric realization; `LogTheta/Indeterminacy.lean` uses an orbit model for Ind3. | **interface/claim only**. The finite/group-theoretic and numerical lemmas are useful, but the real etale-theta, prime-strip, Kummer, and initial-data constructions are not recovered from the original geometry. |
| [lana-project/iut4-sec1](https://github.com/lana-project/iut4-sec1) `a7551d2` (refreshed 2026-08-04; unchanged) | 26 Lean files. Six Mathlib-only Section-1 targets are exported. The comparator README marks later targets (tensor bijection/norm, second error, exact prime-counting) as not included or conditional. | **proved only for elementary Section 1 fragments**. It intentionally does not verify IUT I--III or Corollary 3.12. |
| [com-junkawasaki/iut-lean](https://github.com/com-junkawasaki/iut-lean) `ca4c0dd` (refreshed 2026-08-04; unchanged) | 7 Lean files. Genuine `Polynomial.abc`/Mason--Stothers corollary and numerical hyperbolic curve-type facts. | **not IUT formalization**; no prime strips or Corollary 3.12 objects. |
| [PriestAmbrose/IUT-Corollary3_12-Lean](https://github.com/PriestAmbrose/IUT-Corollary3_12-Lean) `e5d5d20` (refreshed 2026-08-04; unchanged) | 5 Lean files. Axioms-first skeleton; `Cor312.lean` has the abstract theorem with `sorry`. | **claim only**; useful as a dependency ledger, not evidence for the disputed implication. |

These repositories are complementary rather than independent completed proofs:
the closest source-facing implementation is promachina's, the most explicit
axioms/deferral ledger is Takkun's, iut4-sec1 covers elementary downstream
arithmetic, and the other two are scaffolds or unrelated proven mathematics.
The four decisions used below are `direct-proof`, `migrated-proof`,
`interface-only`, and `excluded`; packaging or regression declarations are not
counted as mathematical progress.

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
- 2026-08-04: refreshed all five public implementation repositories. The
  default branches of Takkun `9d56c46`, LANA `a7551d2`, com-junkawasaki
  `ca4c0dd`, and PriestAmbrose `e5d5d20` are unchanged. Promachina was first
  refreshed at `36ef280d`; a second refresh found `581e2b89` (189 Lean files),
  ten commits after the fixed local snapshot `0d52e0fd`.
- 2026-08-04: directly applied the exact promachina countable-base patch for
  `SourceFiniteSheetSemiGraphCover`, `SourceGluedGaloisLevelSystem`,
  `SourceCombinatorialUniversalCover`, and
  `SourceSemiGraphResidualSeparation`. The patch proves finite projection
  fibers and replaces unnecessary finite-base hypotheses by countability; it
  introduces no record obligation. The four modules pass with zero output in
  `logs/lean/serial-20260804-054453/summary.json` and
  `logs/lean/serial-20260804-054422/summary.json`.
- 2026-08-04: audited the new bad-local stable-reduction files separately.
  Their finite semigraphs and compact/noncompact glued-cover equivalences are
  actual constructions, but `SourceTateNodalTameRealization`,
  `FiniteEtaleQuotientRealization`, `SourceTateNodalProSigmaCompletion`, and
  `SourceTateNodalHyperbolicProSigmaFacts` store the decisive geometric and
  group-theoretic facts as fields. Consequently the five Example-2.10-style
  conclusions remain `interface-only` and are not counted toward the 3.11 to
  3.12 wall.
- 2026-08-04: the 27-file imported foundation closure compiles topologically.
  After removing the only two unused simp arguments, the affected upper
  closure is warning-free in `logs/lean/serial-20260804-053109/summary.json`.
  The expanded `#print axioms` audit passes without `sorryAx` at
  `logs/lean/axioms-upstream-foundations-20260804-054745/`; the entire
  `Iut/Foundations` tree contains zero custom top-level `axiom`/`opaque`
  declarations.
- 2026-08-04: the final post-port topology-ordered run is
  `logs/lean/serial-20260804-055402/summary.json`: 27/27 exit code 0 and all 54
  module logs empty. This is the authoritative warning-free closure evidence.
- 2026-08-04: audited promachina commits `c8c4a4b4` and `18e1ad97` at refreshed
  HEAD `581e2b89`. `SourceAndreTemperedExactSequence` stores inclusion
  injectivity, projection surjectivity/openness, exactness, both profinite
  completion universal properties, completion injectivity, and commuting
  squares in `SourceAndreTemperedFundamentalGroupPrerequisite`.
  `SourceBadLocalArithmeticTemperedTower` genuinely proves quotient
  transitions and canonical-map injectivity from an exhaustive kernel, but
  stores stable-log specialization, specialization surjectivity, normality,
  level exactness, limit surjectivity, and inducing topology as fields. The
  wrappers are therefore `interface-only`; only the generic group-theoretic
  kernels are extraction candidates. The declaration audit is recorded in
  `vendor/promachina/review-581e2b89.json`.
- 2026-08-04: refreshed promachina again at `c7c06e23` (190 Lean files) and
  audited commit `198de794`. Its new selected finite-place covering boundary
  proves the bad/good set partition and derives categories, functors,
  adjunctions, and full faithfulness from supplied branch data. The selected
  bad-place family still stores the stable-reduction, Andre, and arithmetic
  tower realizations as fields, so the wrapper remains `interface-only`.
  Declaration-level details are in `vendor/promachina/review-c7c06e23.json`.
- 2026-08-04: mechanically ported the genuinely constructed lower layer used
  by that wrapper: connected finite covering categories, kernel orbits,
  countable temperoids, and the kernel-orbit/restriction adjunction. The first
  three files are byte-identical to the fixed source snapshot. The fourth has
  only a Lean 4.32.2 instance-interface migration: two non-inferable `Full`
  instances became explicit theorems installed locally by `letI`; hypotheses
  and proof bodies are unchanged. A SHA-guarded extraction also separates the
  generic nested-normal-quotient system from the conditional arithmetic tower.
- 2026-08-04: the combined five-module closure is warning-free in
  `logs/lean/serial-20260804-063139/summary.json` (5/5, ten empty logs). The
  expanded axiom audit passes without `sorryAx` in
  `logs/lean/axioms-upstream-foundations-20260804-063457/`; every sampled new
  declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.
  Provenance is recorded in `vendor/promachina/selective-ports-c7c06e23.json`;
  the 31-file compatibility manifest has 20 patched and 11 byte-identical
  files, and all 20 patches pass reverse application checks.
- 2026-08-04: ported the literal tempered-deck construction and its two
  surjectivity layers from `promachina@c7c06e23`. The source proves local
  universal-tree lifting, finite bounded lift fibers, cofiltered compatible
  sections, refinement-transition surjectivity, and raw/literal inverse-limit
  projection surjectivity. The three-module serial run is 3/3 with six empty
  logs at `logs/lean/serial-20260804-065656/summary.json`. Ten representative
  declarations have no `sorryAx` and use only `propext`, `Classical.choice`,
  and `Quot.sound` in
  `logs/lean/axioms-upstream-foundations-20260804-065850/`. Exact hashes and
  the two compatibility diffs are recorded in
  `vendor/promachina/selective-ports-tempered-deck-c7c06e23.json`. This closes
  a genuine tempered-deck foundation layer, not the stable/Andre/arithmetic
  realization or any IPL/SHE/APT and log-volume obligation.
- 2026-08-04: refreshed every public branch after the deck port. Remote
  `master` remains `c7c06e23`; 24 of 25 non-master branch tips are ancestors
  of it, and the sole unmerged tip `7a0854b2` has exactly the same Git tree as
  its parent. No additional mathematical file is available to port.
- 2026-08-04: closed the five-module Galois-splitter-to-geometric-domination
  batch under Lean/Mathlib 4.32.2. The serial run is 5/5 with ten empty logs
  at `logs/lean/serial-20260804-080846/summary.json`; the representative axiom
  audit passes without `sorryAx` at
  `logs/lean/axioms-upstream-foundations-20260804-081211/`. This is recorded
  as a proved alternative construction kernel for *Semi-graphs of
  Anabelioids*, Proposition 3.6(ii), while exact identity/equivalence with the
  paper's complete objects remains a separate semantic audit obligation.
- 2026-08-04: closed the complete 26-module tempered/action-cover batch from
  action factorization through the full and faithful action-cover functor.
  The aggregate evidence consists of six topology-ordered serial runs ending
  at `logs/lean/serial-20260804-085836/summary.json`: 26/26 exit code 0 and all
  52 module logs empty. The expanded endpoint audit passes without `sorryAx`
  at `logs/lean/axioms-upstream-foundations-20260804-090536/`. Exact source
  and production SHA-256 values are recorded in
  `vendor/promachina/selective-ports-tempered-action-cover-c7c06e23.json`.
  This is not counted as IUT III Theorem 3.11 or Corollary 3.12.
- 2026-08-04: added the algebraic `xmu` quotient required by IUT II,
  Definition 4.9(i), in `IUTII/Kummer/TimesMuQuotient.lean`. For an actual
  commutative unit group, Lean forms the quotient by `CommGroup.torsion`,
  proves the quotient map surjective with exactly that kernel, proves every
  multiplicative automorphism preserves torsion, descends an arbitrary group
  action, and proves equivariance, the identity/composition laws, and that the
  quotient is torsion-free. The `FPrimeStrip` bridge first takes the canonical
  unit group of its value monoid and lifts the existing action via
  `Units.mapEquiv`; this avoids assuming an unrelated group structure on the
  monoid and follows the source's `O^x(A)/O^mu(A)` construction. No topology,
  ind-system, Ism-orbit, or Kummer isomorphism is asserted here.
- 2026-08-04: the first `xmu` compile log at
  `logs/lean/serial-20260804-095002/summary.json` records the rejected direct
  `CommGroup (F.Mon v)` bridge: Lean correctly exposed that its multiplication
  need not be definitionally the `FPrimeStrip` multiplication. The canonical
  unit-group revision compiles warning-free with empty stdout/stderr in
  `logs/lean/serial-20260804-095354/summary.json`.
- 2026-08-04: the production entry passed with empty stdout/stderr in
  `logs/lean/serial-20260804-095517/summary.json`. The expanded endpoint audit
  is `logs/lean/axioms-20260804-095813/axiom_audit.stdout.log`: every new
  theorem uses only `propext`, `Classical.choice`, and `Quot.sound`, while the
  strict boundary still contains exactly the single pre-existing Step-XI
  `sorryAx`; see `logs/lean/boundary-20260804-095813.log`. The production tree
  has zero custom top-level `axiom`/`opaque` declarations in
  `logs/lean/custom-axiom-20260804-095802.log`.
- 2026-08-04: refreshed `promachina/iut-lean` again at `ea91200b`, two commits
  after the prior `bbb736cd` audit. The new selected-place base-change batch
  derives local curves, quotient stacks, pullback functors, selected-place
  stabilizer images, and indexed local cover/cusp/theta-root diagrams from
  tighter preceding data. It does not alter the Definition 4.9(i) quotient/Ism
  kernel, whose source file was last changed at `3de1d7c1`. The selected local
  constructions are candidates for the later initial-theta/Hodge-theater use
  point, not a reason to import the 857-line wrapper now.
- 2026-08-04: adapted the reusable Definition 4.9(i) Ism kernel into
  `IUTII/Kummer/TimesMuIsm.lean`. For arbitrary actual group actions, Lean now
  constructs each open-subgroup fixed group and its image modulo torsion,
  proves the image is pointwise fixed, constructs the exact equivariant and
  image-preserving Ism subgroup, constructs its action on compatible Kummer
  isomorphisms, and proves all compatible representatives define the same
  orbit. It constructs the identity representative for one action but does not
  assert that the paper's group-theoretic and Frobenioid actions are isomorphic.
  Source attribution and the exact semantic boundary are recorded in
  `vendor/promachina/selective-port-times-mu-ea91200b.json`.
- 2026-08-04: the first Ism adaptation log
  `logs/lean/serial-20260804-100541/summary.json` records only Lean 4.32.2
  coercion/noncomputability migration failures. The corrected module is
  warning-free with empty stdout/stderr in
  `logs/lean/serial-20260804-100702/summary.json`; no mathematical assumption or
  conclusion changed in the correction.
- 2026-08-04: the production entry after the Ism port passed with empty
  stdout/stderr in `logs/lean/serial-20260804-100833/summary.json`. The seven
  new endpoint samples in
  `logs/lean/axioms-20260804-100903/axiom_audit.stdout.log` use only `propext`,
  `Classical.choice`, and `Quot.sound`; the strict boundary still reports only
  the one pre-existing Step-XI `sorryAx` in
  `logs/lean/boundary-20260804-100903.log`. The post-port custom declaration
  scan reports zero top-level `axiom`/`opaque` declarations in
  `logs/lean/custom-axiom-20260804-100931.log`.
- 2026-08-04: added the target-directed local-field `G_m` Kummer-rigidity
  chain in `IUTII/Kummer/LocalFieldRigidity.lean`, selected from the corrected
  upstream faithfulness split at `3de1d7c1`. Lean proves residual-finiteness
  root rigidity, realizes valuation-ring units as a profinite group, proves a
  full local-field unit with roots of every positive degree has zero discrete
  valuation and is the identity, and derives injectivity of any multiplicative
  Kummer map with the standard kernel characterization. It does not state or
  prove the stronger arbitrary-torus or semi-abelian clauses. Exact source
  blobs, exclusions, and scope are recorded in
  `vendor/promachina/selective-port-local-field-kummer-ea91200b.json`.
- 2026-08-04: the initial local-field rigidity log
  `logs/lean/serial-20260804-101250/summary.json` records one mistyped quotient
  symbol and two Lean 4.32.2 explicit-argument migrations. The corrected module
  compiles warning-free with empty stdout/stderr in
  `logs/lean/serial-20260804-101448/summary.json`; no theorem statement or
  mathematical step changed.
- 2026-08-04: the production entry after the local-field rigidity addition
  passed with empty stdout/stderr in
  `logs/lean/serial-20260804-101553/summary.json`. The six new endpoint samples
  in `logs/lean/axioms-20260804-101648/axiom_audit.stdout.log` use only
  `propext`, `Classical.choice`, and `Quot.sound`; the strict boundary still
  reports exactly the one pre-existing Step-XI `sorryAx` in
  `logs/lean/boundary-20260804-101648.log`.
- 2026-08-04: the post-local-field custom declaration scan reports zero
  top-level production `axiom`/`opaque` declarations in
  `logs/lean/custom-axiom-20260804-101945.log`.
- 2026-08-04: added `Iut/Foundations/ContinuousH1.lean`,
  `IUTII/Kummer/RationalRootSystem.lean`, and
  `IUTII/Kummer/ContinuousKummerGerm.lean`. Lean now constructs continuous
  `H^1` germs, one coherent rational root system, the root-ratio crossed
  homomorphism for an open-subgroup-fixed unit, its continuity, and its
  independence from the compatible-root choice. No Frobenioid evaluation or
  group/Frobenioid Kummer isomorphism is inferred.
- 2026-08-04: the four-module production closure is warning-free with eight
  empty logs in `logs/lean/serial-20260804-104828/summary.json`. The expanded
  axiom audit in `logs/lean/axioms-20260804-105006/axiom_audit.stdout.log`
  reports only `propext`, `Classical.choice`, and `Quot.sound` for the new
  endpoints; the production boundary still has exactly the one pre-existing
  Step-XI `sorryAx`. Both custom-declaration scans report zero declarations in
  `logs/lean/custom-axiom-20260804-105339.log` and
  `logs/lean/custom-axiom-foundations-20260804-105339.log`. Exact source and
  production hashes and exclusions are recorded in
  `vendor/promachina/selective-port-continuous-kummer-ea91200b.json`.
- 2026-08-04: added `IUTII/Kummer/CanonicalKummerMap.lean`. The canonical
  construction proves open stabilizers, common-subgroup/root-system
  independence, product-root compatibility, and a genuine group homomorphism
  from all divisible discrete coefficient units to the continuous Kummer-germ
  group. The affected closure is 4/4 with empty diagnostics in
  `logs/lean/serial-20260804-110554/summary.json`. The expanded endpoint audit
  passes in `logs/lean/axioms-20260804-110734/axiom_audit.stdout.log`; only the
  pre-existing Step-XI `sorryAx` remains. The production hash is recorded in
  `vendor/promachina/selective-port-continuous-kummer-ea91200b.json`.
- 2026-08-04: added `IUTII/Kummer/LocalGaloisKummerAction.lean`. With the
  Krull topology on `Gal(Qbar_p/Q_p)` and an explicit discrete topology on
  algebraic-closure units, Lean identifies unit and field stabilizers and
  applies Mathlib's integral-extension stabilizer theorem. The resulting
  local action and group-side Kummer homomorphism compile warning-free in
  `logs/lean/serial-20260804-111713/summary.json`. The source's ind-topological
  integral monoid and Frobenioid evaluation remain outside this module.
- 2026-08-04: the five-module affected closure through `Project.lean` passes
  with 10/10 empty diagnostic logs in
  `logs/lean/serial-20260804-111855/summary.json`. The expanded endpoint audit
  passes in `logs/lean/axioms-20260804-112123/axiom_audit.stdout.log`; the only
  `sorryAx` is still `theorem311_produces_stepXI_contract`. The production and
  imported-foundation custom-declaration scans both report zero in
  `logs/lean/custom-axiom-20260804-112206.log` and
  `logs/lean/custom-axiom-foundations-20260804-112206.log`.
- 2026-08-05: refreshed `promachina/iut-lean` from the previously audited
  `ea91200b` to `2eb61e1b` (16 commits, 29 changed files, 20 Lean files, 26
  remote branches). The new batches cover Tate coefficients, nonarchimedean
  and global Frobenioid reconstruction packages, archimedean local geometry,
  bad-place evaluation sections, and a D-theta bridge. The changed Lean tree
  has no top-level `axiom`, `opaque`, or explicit `sorry`, but the decisive
  analytic geometry, Andre splitting, reconstruction, and local/global
  Frobenioid existence remain fields of prerequisite/reconstruction records.
  The declaration-level decision is recorded in
  `vendor/promachina/review-2eb61e1b.json`; these wrappers were not bulk-ported.
- 2026-08-05: added `LocalTorsionCyclotome.lean`. The exact upstream
  rational-circle/root-of-unity proof was adapted only for the Lean 4.32.2
  `CommGroup.mem_torsion` API, then specialized to the already proved local
  integral monoid. Lean proves `Q/Z` equivalent to its full torsion-unit group,
  transports algebraic-closure divisibility to `RootableBy Nat` on the actual
  Grothendieck groupification, and constructs one coherent rational-root
  system. No cyclotomic equivalence is accepted as input.
- 2026-08-05: added `LocalMLFTMPair.lean`. The canonical model uses the actual
  Krull-topological `Gal(Qbar_p/Q_p)`, continuous identity augmentation, local
  integral monoid, and its proved action. Every model augmentation pulls back
  the genuine Krull-open stabilizer, and Lean proves the pullback fixes its
  element. The induced unit and `times-mu` actions instantiate the existing
  Ism kernel, while the group/Frobenioid Kummer comparison remains unasserted.
- 2026-08-05: corrected `LocalIntegralFPrimeStrip.Mon` from the unit group of
  the integral monoid to the integral monoid itself. The previous wrapper
  caused the generic Kummer layer to take units twice. The new
  `LocalMLFPrimeStripBridge.lean` proves by definitional equality that the
  corrected strip's monoid, unit, and `times-mu` actions are exactly those of
  the canonical MLF `TM` pair. This changes the local wrapper to the intended
  mathematical carrier; it does not alter any lower theorem or infer a
  categorical Frobenioid evaluation.
- 2026-08-05: fetched all public `promachina/iut-lean` branch refs after the
  local `TM`/prime-strip bridge closed. `master` remained at `2eb61e1b`; the
  newly visible refs are older work branches, and all except the tempered
  semigraph inverse-limit branch are already merged into `master`. The
  upstream ledger itself still marks construction from Frobenioid evaluation
  and finite/archimedean reconstruction outputs as open, so no reconstruction
  wrapper was imported. The reusable groupification-action proof was instead
  specialized to our actual local monoid in `LocalGroupificationAction.lean`.
  Its action, Krull-open stabilizer, discrete continuity, unit embedding, and
  comparison with algebraic-closure units are all proved without new
  assumptions. The branch-level decision is recorded in
  `vendor/promachina/review-branches-20260805.json`.
- 2026-08-05: the final affected module logs are in
  `logs/lean/build-serial-20260805-010000`; all final stdout/stderr diagnostics
  are empty. The expanded audit at
  `logs/lean/axioms-20260805-010000/axiom_audit.stdout.log` reports only
  `propext`, `Classical.choice`, and `Quot.sound` for every new theorem. Its
  only `sorryAx` remains
  `LeanFormal.IUT.theorem311_produces_stepXI_contract`. The final aggregate
  log `logs/lean/build-20260805-010000/LeanFormal.stdout.log` reports
  `Build completed successfully (3729 jobs)`; stderr is empty and the combined
  warning/error scan has zero matches. The C-layer ledger now contains 24
  proved, 6 interface, and 5 pending obligations (24/35 unweighted; about 40%
  by remaining mathematical work).
- 2026-08-05: `LocalGroupificationAction.lean` passed its standalone Lake
  build, the production `Project` target, and the full `LeanFormal` build
  (`3730` jobs). Final logs are under
  `logs/lean/local-groupification-20260805/`; the initial missing-olean build
  ordering diagnostic is retained separately as
  `Project.initial-missing-olean.log`. The final module, project, and aggregate
  logs contain no warning or error. `axiom_audit.log` reports only `propext`,
  `Classical.choice`, and `Quot.sound` for all six sampled declarations from
  the new module. Production still has no custom top-level `axiom` or
  `opaque`; its sole explicit `sorry` and sole audited `sorryAx` remain the
  `theorem311_produces_stepXI_contract` bridge.
- 2026-08-05: completed the actual local integral-unit Kummer map and its
  mono-analytic injectivity theorem. Root-choice comparison is an explicit
  coboundary, multiplication is proved on common open subgroups, and a trivial
  germ yields roots of every degree in one finite fixed field. The residual-
  finiteness step uses a proved ring equivalence between the canonical
  valuation ring of `Q_p` and Mathlib's `Z_p`, not an assumed local-field
  instance. The three new C-layer obligations are proved without `sorryAx`;
  Frobenioid-side evaluation and the IUT II Definition 4.9 comparison remain
  pending. Final target, Project, axiom, custom-axiom, and aggregate logs are
  under `logs/lean/local-unit-kummer-injectivity-20260805/`; the aggregate is
  3738 jobs with zero diagnostics. The C-layer ledger is now 27 proved, 6
  interface, and 5 pending obligations (27/38 unweighted; approximately 43%
  by remaining mathematical work).
- 2026-08-05: fetched `promachina/iut-lean` through `7bea5b03`. The new Topics I
  chain and Definition 5.2 coric files are axiom/sorry-free, but their exported
  reconstructions select candidates from supplied recognition existence and
  uniqueness fields. They are retained as a specification and future source
  of derived constructors, not bulk-ported. The precise intersection with the
  newly proved Kummer injectivity and the remaining prerequisites is recorded
  in `vendor/promachina/review-7bea5b03.json`.
- 2026-08-05: checked IUT II, Definition 4.9(i), directly on source PDF pages
  153--155 and added `LocalIntegralUnitEvaluationImage.lean`. Lean proves that
  the concrete local unit evaluation has exactly the algebraic-closure units
  whose value and inverse are integral. The induced multiplicative equivalence
  is Galois-equivariant, descends to the full-torsion quotient, and preserves
  every open-subgroup invariant image, producing a real carrier-level `Ism`
  orbit. This does not claim that the carrier is the paper's `O^triangle(A)`:
  the universal-cover pro-object, categorical Frobenioid evaluation,
  ind-topology, and group-reconstruction identification remain pending.
- 2026-08-05: the new local evaluation-image target and production `Project`
  build passed with zero diagnostics; the latter completed 3737 jobs. The full
  `LeanFormal` build completed 3739 jobs. Logs are under
  `logs/lean/local-integral-unit-evaluation-image-20260805/`. The four sampled
  new endpoints use only `propext`, `Classical.choice`, and `Quot.sound`;
  custom top-level `axiom`/`opaque` remains zero, and the only production
  `sorryAx` is still `theorem311_produces_stepXI_contract`.
- 2026-08-05: fetched the one-commit-ahead upstream F-bridge branch
  `87d595c7`. Its Definition 5.5 design removes caller-supplied selected
  F-arrows and injectivity fields, then derives the selected range and its
  associated-D uniqueness from reconstructed pullback lifts. The pullback,
  global Frobenioid restriction, local-to-global lifts, and theater
  isomorphisms still originate in `candidate_exists` recognition records, and
  Definition 5.5(iii) gluing is absent. No code was ported; the reusable kernel
  and exact boundary are recorded in `vendor/promachina/review-87d595c7.json`.
- 2026-08-05: selectively ported the byte-identical Apache-2.0 source file
  `SourceFrobenioidRationalMonoidTransport.lean` from upstream commit
  `5e70fbe9` (audited snapshot `87d595c7`). It derives the restriction of
  Frobenioids I, Proposition 2.2(ii), to `(C^istr)^lin`, together with (iv),
  from `FrobenioidPresentation.axioms`: pullback on rational endomorphism
  monoids, its identity/composition laws, and injective extension across
  isotropic hulls. No Lean/Mathlib migration was required and no unrelated
  Frobenioid reconstruction wrappers were imported. Provenance is
  recorded in `vendor/promachina/selective-port-rational-monoid-87d595c7.json`.
- 2026-08-05: the rational-monoid transport source and `Project.lean` passed
  their logged 2/2 closure with empty diagnostics. Both foundation and
  production axiom audits report only `propext`, `Classical.choice`, and
  `Quot.sound` for the new endpoint. Aggregate builds completed at 3740 and
  3742 jobs with zero warning/error matches; the sole production `sorryAx`
  remains `theorem311_produces_stepXI_contract`.
- 2026-08-05: refreshed all public upstream branch refs after completing the
  rational-monoid transport step. Master advanced to merge commit `f87990b4`,
  whose tree is identical to the already audited F-bridge head `87d595c7`.
  Thus the refresh contains no unreviewed code: its recognition-record boundary
  and the decision not to port it now are unchanged. The merge audit is in
  `vendor/promachina/review-f87990b4.json`.
- 2026-08-05: added `SourceFrobenioidIsotropicBase.lean` after checking the
  exact text of Frobenioids I, Proposition 2.2 and IUT II, Definition 4.9.
  The module constructs the literal category `D*`, proves its projection to
  the Frobenioid base full, faithful, and essentially surjective, and packages
  the resulting equivalence `D* ≃ D`. The full `D^op -> Mon` functor and its
  universal-pro-object colimit are deliberately not asserted yet.
- 2026-08-05: added `SourceFrobenioidCoAngularBaseChange.lean`. It turns the
  Definition 1.3(i)(b) common pre-step into the isotropic common co-angular
  witness used in the proof of Proposition 2.2(ii), by passing through an
  isotropic hull. It also derives identity and composition coherence for the
  axiom-selected unit transport from its uniqueness clause. Choice independence
  and the full base-category rational-monoid functor remain explicit next steps.
- 2026-08-05: final verification of the isotropic-base and co-angular
  base-change modules passed. Their logged 2/2 closures have empty diagnostics;
  the four new sampled endpoints depend only on `propext`, `Classical.choice`,
  and `Quot.sound`. The latest `Project` and `LeanFormal` aggregates completed
  successfully at 3742 and 3744 jobs, and the only production `sorryAx` remains
  `theorem311_produces_stepXI_contract`.
- 2026-08-05: completed the base-isomorphism coherence omitted from the prior
  entry. Common-witness transport is now choice-independent and satisfies
  identity, inverse, and composition laws. Added
  `SourceFrobenioidBasePullbackLift.lean`: Definition 1.3(i)(c) now constructs
  an isotropic pullback representative for every base arrow, and Lean proves
  both `map_id` and independence from the selected pullback representative.
  The noninvertible composition law is not claimed: its remaining obligation
  is the mixed naturality square between pullback transport and co-angular
  pre-step transport. The five-module logged closure is
  `logs/lean/serial-20260805-044224/summary.json`; after correcting one audit
  declaration namespace, the final foundations audit is
  `logs/lean/serial-20260805-044431/summary.json`.
- 2026-08-05: mechanically ported the seven-file Frobenioids I Theorem 5.2
  model chain from the fixed Apache-2.0 public snapshot. The final presentation
  constructs every Definition 1.3 axiom group from the rational-function and
  divisor input; none of those conclusions is supplied as input. Six files are
  byte-identical and the divisor-order file has only two explicit object
  annotations required by Lean 4.32.2.
- 2026-08-05: constructed the reusable nonzero integral-closure monoid for an
  actual valued field, its absolute Galois action, fraction-field theorem, and
  Grothendieck-group equivalence with algebraic-closure units. The existing
  `LocalIntegralMonoid p` is proved equivalent and Galois-compatible.
- 2026-08-05: replaced the public Definition 5.2 local reconstruction's broad
  dependency on `SourceTheorem311` by the exact finite-place completion base.
  The five-file chain now proves the finite Galois stage colimit, the integral
  stage exhaustion, continuous and jointly continuous Krull action,
  equivariant transitions, and a natural-number-indexed cofinal subsystem.
  One continuity file remains byte-identical; all other changes are recorded
  Lean 4.32.2 coercion or wrapper migrations. The exact hashes and migration
  descriptions are in
  `vendor/promachina/selective-port-model-frobenioid-definition52-0d52e0fd.json`.
- 2026-08-05: the integrated production closure completed at 3803 jobs and the
  full `LeanFormal` aggregate at 3805 jobs with no warning or error matches.
  Both axiom audits show only `propext`, `Classical.choice`, and `Quot.sound`
  for every new sampled endpoint; the custom declaration scan is zero. The
  sole project `sorryAx` remains `theorem311_produces_stepXI_contract`.
- 2026-08-05: the C-layer work-weighted estimate is now approximately 55--58%.
  The next source-specific obligation is not another generic local lemma: it is
  to construct the actual MLF/CAF Frobenioid and prove that its universal-pro
  categorical `O^triangle(A)` evaluation, Galois action, and ind-topology agree
  with the completed finite-place reconstruction. Initial theta existence,
  complete Hodge theaters and histories, theta-links, and log-links remain
  subsequent C-layer obligations.
- 2026-08-06: completed the finite-stage model Frobenioid input and rebuilt its
  Lake cache. `SourceFiniteStageModelFrobenioid.lean` now supplies a genuine
  universe-correct sharp/saturated divisor monoid, ramification-weighted
  Grothendieck pullback, rational-function additive system, and proved divisor
  naturality. The target build `lake build
  Iut.Foundations.SourceFiniteStageModelFrobenioid` completed successfully
  (`3406` jobs); the cached production target
  `lake build LeanFormal.IUT.Project` completed successfully (`3820` jobs).
  The direct Project closure and both production/upstream foundation axiom
  audits were then run serially with `lake env lean -j 1`; all exited `0` with
  empty stderr. Logs are under
  `logs/lean/serial-20260806-0218/`. The new endpoints
  `stageDivisorialMonoidOn`, `stageDivisorGrothendieckPullback_apply`, and
  `stageModelInput` depend only on `propext`, `Classical.choice`, and
  `Quot.sound`; the sole production `sorryAx` remains
  `LeanFormal.IUT.theorem311_produces_stepXI_contract`. The audit references
  use root-qualified names so that the cached Project import cannot shadow the
  `Iut` namespace.
- 2026-08-06: added `SourceFiniteStageModelEvaluation.lean` by mechanically
  promoting a standalone zero-diagnostic prototype. It proves the equality
  between the model's effective rational-function submonoid and the
  normalized-valuation nonnegative submonoid, then composes the generic model
  zero-object equivalence with the proved finite-stage integral-monoid
  equivalence. The module build completed successfully (`3414` jobs), the
  cached Project build completed successfully (`3821` jobs), and the direct
  Project closure plus production and upstream foundation axiom audits all
  exited `0` with empty stderr. The new endpoints use only `propext`,
  `Classical.choice`, and `Quot.sound`; no new `sorryAx` or custom axiom was
  introduced. Logs are under `logs/lean/serial-20260806-0230/`.
  The custom declaration scan was rerun at 2026-08-06 01:29:57 CST and
  reported `customAxiomDeclarations: 0`.
  The complete `lake build LeanFormal` aggregate also completed successfully
  (`3823` jobs); its log is `logs/lean/serial-20260806-0230/aggregate.log`.
- 2026-08-06: replaced the finite-stage effective-to-integral equivalence's
  proof-irrelevant submonoid transport with an explicit `MulEquiv`, then proved
  `stageModelEffectiveRationalFunctionEquivIntegralMonoid_natural`: the model
  effective pullback along every opposite-stage arrow agrees on the nose with
  the actual `stageIntegralTransition` after evaluation. This is a genuine
  finite-stage naturality square, not an ind-limit or MLF/CAF identification.
  The module target (`3422` jobs), Project target (`3821` jobs), direct Project
  closure, production/upstream axiom audits, custom-axiom scan, and complete
  `LeanFormal` aggregate (`3823` jobs) all exited `0`; all Lean stderr logs are
  empty. Logs are under `logs/lean/serial-20260806-0340/`. The new naturality
  theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-06: exposed the finite-stage square as actual functorial data:
  `stageIntegralMonoidFunctor` is the genuine `MonCat` functor of nonzero
  integral stages, `stageModelEffectiveToIntegralNatIso` is a proved natural
  isomorphism from the model effective functor, and
  `stageModelZeroObjectToIntegralNatIso` composes it with the model
  `zeroRationalMonoidFunctor`/effective natural isomorphism. The module target
  (`3422` jobs), Project target (`3821` jobs), direct Project closure,
  production/upstream axiom audits, custom declaration scan, and full
  `LeanFormal` aggregate (`3823` jobs) all exited `0` with empty Lean stderr.
  Logs are under `logs/lean/serial-20260806-0405/`; the new functor and
  natural-isomorphism endpoints use only `propext`, `Classical.choice`, and
  `Quot.sound`. This still stops before the categorical MLF/CAF evaluation and
  the ind-colimit comparison.
- 2026-08-06: completed the finite-stage ind-limit bridge. The production
  evaluation module now constructs the actual filtered `MonCat` colimit of
  the stage integral functor, a cocone into `IndIntegralMonoid`, and a
  colimit-to-limit monoid hom. Using Mathlib's filtered representative
  relation, the proved stage-transition compatibility, injectivity, and the
  previously proved stage exhaustion, Lean establishes both surjectivity and
  injectivity and packages the result as
  `stageIntegralFilteredColimitEquivInd`. This is a genuine categorical
  colimit identification for the reconstructed integral carrier; it is not yet
  the paper's MLF/CAF `O^triangle` evaluation theorem. The module target
  (`3424` jobs), Project target (`3823` jobs), direct Project closure,
  production/upstream axiom audits, custom declaration scan, and full
  `LeanFormal` aggregate (`3825` jobs) all exited `0` with empty Lean stderr.
 Logs are under `logs/lean/serial-20260806-0425/`; all new endpoints use only
 `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-08-06: lifted the proved finite-stage natural isomorphism from the model
  `zeroRationalMonoidFunctor` to the actual filtered `MonCat` colimit. The new
  `stageModelZeroObjectToIntegralCocone` and its inverse cocone give explicit
  colimit maps; their two composites are proved by the filtered-colimit
  universal property, yielding
  `stageModelZeroObjectFilteredColimitIsoIntegral` and the genuine monoid
  equivalence `stageModelZeroObjectFilteredColimitEquivInd` with
  `IndIntegralMonoid`. The source-specific categorical MLF/CAF identification
  is still not claimed. The module was compiled serially in
  `logs/lean/serial-20260806-continue-6/`; no `sorry`, custom axiom, or opaque
  declaration was added.
- 2026-08-06: verified the colimit lift in the complete project closure. The
  finite-stage module, `LeanFormal.IUT.Project`, production axiom audit,
  upstream-foundations axiom audit, custom declaration scan, and `lake build
  LeanFormal` all exited `0`; the aggregate build completed at `3825` jobs and
  all Lean stderr logs are empty. Logs are under
  `logs/lean/serial-20260806-continue-7/`. The new colimit equivalence depends
  only on `propext`, `Classical.choice`, and `Quot.sound`; the sole production
  `sorryAx` remains `LeanFormal.IUT.theorem311_produces_stepXI_contract`.
- 2026-08-06: composed the verified model-colimit equivalence with the existing
  algebraic identification `indIntegralMonoidEquivSourceMLF`, producing
  `stageModelZeroObjectFilteredColimitEquivSourceMLF`. This is a carrier-level
  bridge to the explicitly constructed nonzero integral elements of the
  algebraic closure; it is not yet the paper's categorical MLF/CAF realization
  or a claim about the full `O^triangle` Frobenioid.
- 2026-08-06: rebuilt the complete closure after the carrier bridge. The module,
  Project target, direct Project closure, both axiom audits, custom declaration
  scan, and aggregate `lake build LeanFormal` all exited `0`; the aggregate
  completed at `3825` jobs with empty Lean stderr. Logs are under
  `logs/lean/serial-20260806-continue-9/`. The new
  `stageModelZeroObjectFilteredColimitEquivSourceMLF` endpoint adds no
  `sorryAx` or custom axiom.
- 2026-08-06: proved the finite-stage index category's missing connectivity
  rather than leaving it as a typeclass premise. `FiniteGaloisIntermediateField`
  has a bottom object; in the opposite stage category `op ⊥` is constructed as
  a terminal object, giving `stageBase_isConnected`. Thin-category arrows are
  proved epimorphisms by the existing Mathlib instance, so the explicit model
  `stageModelPreFrobenioidPresentation` now packages the constructed
  `stageModelInput` as a genuine connected, totally epimorphic
  `PreFrobenioidPresentation`. This is still a pre-Frobenioid presentation:
  the seven Frobenioid axiom groups and categorical MLF/CAF realization remain
  unproved.
- 2026-08-06: verified this pre-Frobenioid block in the complete project. The
  finite-stage model and evaluation modules, Project closure, production and
  upstream foundation axiom audits, custom declaration scan, and aggregate
  `lake build LeanFormal` all exited `0`; the aggregate completed at `3826`
  jobs. All Lean stderr files contain no non-whitespace diagnostics, so this
  block introduces no warnings. Logs are under
  `logs/lean/serial-20260806-model-presentation-6/`. The new endpoints depend
  only on the standard `propext`, `Classical.choice`, and `Quot.sound` family;
  no new `sorryAx`, `axiom`, or `opaque` declaration was added.
- 2026-08-06: promoted the finite-stage endpoint from the verified
  `PreFrobenioidPresentation` to a full `FrobenioidPresentation` by applying
  the existing, fully proved Definition 1.3 axiom package to the concrete
  stage input. The endpoint is
  `stageModelFrobenioidPresentation`; it uses the already proved terminal
  object/connectedness and thin-category epimorphism results, so it adds no
  mathematical assumption. The standalone module compile passed in
  `logs/lean/serial-20260806-025639/`; the Project target passed in
  `logs/lean/run-20260806-025705.status.json`; production and upstream axiom
  audits passed in `logs/lean/axioms-20260806-025759/` and
  `logs/lean/axioms-upstream-foundations-20260806-025822/`; the custom scan
  reported zero declarations in
  `logs/lean/custom-axioms-20260806-0301.stdout.log` (with an empty stderr
  log);
  and the complete aggregate passed in
  `logs/lean/run-20260806-025851.status.json`. This is a complete formal
  Frobenioid presentation for the finite-stage model, not yet the paper's
  categorical MLF/CAF realization or an IUT-specific Theorem 3.11 input.
- 2026-08-06: added `IUTI/InitialTheta/ConcreteArithmeticExample.lean`.
  Lean constructs the quadratic field `Q(i)` as an `AdjoinRoot`, proves the
  irreducibility and square-root relation, obtains the number-field/Galois and
  finite-dimensional identity-tower instances, and supplies a nonsingular
  Weierstrass model as a `PuncturedEllipticCurve`. The standalone check passed
  with exit code `0` and empty diagnostics in
  `logs/lean/concrete-initial-theta-20260806-031842.*`; after materializing its
  `.olean`, the direct `Project.lean` closure also passed with exit code `0` in
  `logs/lean/project-concrete-theta-20260806-031951.*`. This upgrades one
  concrete input from interface data to a genuine proved example, but does not
  prove general initial-Theta existence, full Hodge theaters, or any
  IUT-specific Theorem 3.11 obligation.
- 2026-08-06: added `IUTI/HodgeTheater/ConcreteHodgeTheaterExample.lean`.
  The proved `Q(i)` arithmetic input is assembled with the actual local
  F-prime-strip carrier and `FiniteThetaPacket.ofQ` to form a concrete
  `HodgeTheater`; a reflexive `ThreeTheaterSystem` and its q-transport theorem
  are also checked. This is a carrier-level instance only. It does not claim
  distinct paper histories, etale/Frobenioid realization, or
  Hodge-Arakelov compatibility.
- 2026-08-06: verified the concrete Hodge-theater example in the complete
  closure. The standalone module, its Lake target, `Project.lean`, and the
  `LeanFormal` aggregate all passed with empty diagnostics; the aggregate
  completed at `3828` jobs (`logs/lean/aggregate-concrete-hodge-theater-20260806-032706.log`).
  The production boundary still reports exactly the single permitted
  `theorem311_produces_stepXI_contract` `sorryAx` in
  `logs/lean/boundary-concrete-hodge-theater-20260806-032744.json`; the
  upstream-foundation audit reports no `sorryAx`, and the custom declaration
  scan reports zero `axiom`/`opaque` declarations.
- 2026-08-06: downloaded the complete `promachina/iut-lean` master snapshot at
  `1fa6387f11fb6dc67eb618b8138e6bc64f56b039` (tree
  `c32abf9c5b85fb44a1815182a465d714a2706972`) into
  `vendor/promachina/snapshots/`. It contains 310 tracked files, 210 Lean
  files, and is licensed Apache-2.0. Relative to the previously audited
  `0d52e0fd`, the upstream diff is 88 files and 34,382 inserted lines. The
  review record is `vendor/promachina/review-1fa6387f.json`; no upstream file
  has been bulk-imported into production. The independent upstream build is
  now passed with exit code `0` at 4443 jobs against its pinned Lean 4.30.0 /
  Mathlib revision. The log is
  `logs/lean/upstream-full-build-1fa6387f-rerun-20260806-052410.log`; it has
  no errors but 109 warnings and 7 deterministic LibrarySuggestions heartbeat
  PANIC messages. The warnings are concentrated in the very large Stage1
  files and do not turn their recognition interfaces into proofs.
- 2026-08-06: the completed upstream source scan found no explicit `sorry`,
  top-level `axiom`, or top-level `opaque` declaration; the two textual
  `opaque` matches are documentation prose. This is separate from the
  source's many recognition/candidate fields, which are ordinary structure
  inputs and remain conditional mathematics rather than hidden axioms.
- 2026-08-06: added `IUTIII/Corollary312/StepXI/HolomorphicHull/WeightedNormalization.lean`.
  It ports only the source-faithful arithmetic core of Remark 3.9.5(vii):
  product common tensor degree, complementary exponents, structure-sheaf
  subtraction, and the exact denominator-clearing normalized log-volume
  equality. It introduces no geometric hull, determinant-line realization,
  Frobenioid identification, or new axiom.
- 2026-08-06: verified the weighted-normalization addition in the complete
  production closure. `Project.lean` passed with exit code `0` and empty
  stderr in `logs/lean/project-check-20260806-055225.*`; `lake build
  LeanFormal` passed at `3829` jobs with empty stderr in
  `logs/lean/build-20260806-055251.*`. The production axiom audit passed in
  `logs/lean/axiom-audit-20260806-055436.*`: exactly one `sorryAx` remains,
  on `theorem311_produces_stepXI_contract`; all sampled foundational and
  downstream arithmetic theorems use only Lean's standard logical axioms.
  The imported upstream-foundation audit passed in
  `logs/lean/upstream-foundations-audit-20260806-055501.*` with zero
  `sorryAx`, and `tools/check_no_custom_axioms.ps1` reports zero custom
  `axiom`/`opaque` declarations at `2026-08-06T05:57:09+08:00`.
- 2026-08-06: added `Foundations/Volumes/HaarLogVolume.lean`. It uses
  Mathlib's actual finite-dimensional additive Haar measure, proves positive
  finite unit closed-ball volume, and proves the exact closed-ball scaling law
  after applying `Real.log`. The generic theorem exposes positivity of the
  normalization explicitly; the `Measure.addHaar` corollary derives it from
  Haar open-set positivity and compactness, so no measure or volume axiom is
  introduced. The standalone compile passed in
  `logs/lean/haar-log-volume-20260806-061317.*`; the aggregate passed at
  `3830` jobs with empty stderr in
  `logs/lean/build-haar-20260806-061418.*`, and `Project.lean` passed in
  `logs/lean/project-haar-20260806-061507.*`. The focused production axiom
  audit passed with the three Haar declarations depending only on
  `propext`, `Classical.choice`, and `Quot.sound`; exactly one unrelated
  `sorryAx` remains at `theorem311_produces_stepXI_contract` in
  `logs/lean/axiom-audit-haar-20260806-061551.*`. The custom declaration scan
  remains zero.
- 2026-08-06: completed the source-foundation aggregate `Iut` without changing
  any mathematical declaration. The five modules that had failed during the
  high-concurrency aggregate (`SourceProfiniteSemiGraphSystem`,
  `SourceTemperoidQuotient`, `SourceTemperoidComponentFamily`,
  `SourceTemperoidAssociatedQuotient`, and `SourceGluedGaloisLevelSystem`)
  each passed as single-module targets. `SourceFiniteSheetUniversalLift` also
  passed when isolated after a process-level aggregate crash. Their logs are
  under `logs/lean/iut-single-*.log`. The final `lake build Iut` completed
  `4194/4194` targets with exit code `0` in
  `logs/lean/build-Iut-root-warning-free-20260806-064339.log`.
- 2026-08-06: resolved the only aggregate style warning by wrapping a long
  proof line in `Iut/Foundations/SourceTemperedGeometricDomination.lean`.
  The repaired module and the full `Iut` aggregate both compile with zero
  warnings; this is a formatting-only change and introduces no axiom, sorry,
  or mathematical premise.
- 2026-08-06: added `IUTII/Frobenioid/ConcreteLocalKummerExample.lean` as the
  next source-facing C-layer unit. It realizes the nontrivial local parameter
  `q = p` inside the actual valuation-ring integral closure and
  `LocalIntegralMonoid`, proves its image in the algebraic-closure units is
  exactly the existing `localQParameterFor`, proves nontriviality after
  Grothendieck groupification, and instantiates the already proved coherent
  rational-root construction at that value. This is a concrete local Kummer
  object, not an etale/Frobenioid theta-link claim. The standalone target
  passed in `logs/lean/concrete-local-q-roots-fix2-20260806-065229.log`; the
  production aggregate passed at `3831` jobs with zero warnings in
  `logs/lean/build-LeanFormal-concrete-local-q-roots-20260806-065257.log`.
- 2026-08-06: extended that same concrete unit with the actual
  `LocalMLFModelTMPair.IntegralKummerRootRealization` for the canonical
  mono-analytic local model and the selected open stabilizer. Its root system
  is the previously proved coherent groupification system, and the specialized
  `root_one` theorem compiles without any new premise. The final standalone
  check is `logs/lean/concrete-local-q-roots-realization-fix2-20260806-065805.log`;
  the full production aggregate is rerun after this unit is closed.
- 2026-08-06: added `IUTI/HodgeTheater/ConcreteIntegralHodgeTheaterExample.lean`.
  It assembles the proved Gaussian arithmetic input, the finite interval
  `[2,7]`, the actual integral `FPrimeStrip`, a reflexive three-theater carrier,
  and the selected nontrivial `q=5` `IntegralKummerRootRealization` into one
  explicit finite input record. The selected place is proved to be the prime
  `5`; no etale, source-history, theta-link, or Frobenioid-recognition claim is
  made. The standalone target passed with zero warnings in
  `logs/lean/concrete-integral-hodge-carrier-final-20260806-070143.log`, and
  `lake build LeanFormal` passed at `3832` jobs with zero warnings in
  `logs/lean/build-LeanFormal-concrete-integral-hodge-final-20260806-070208.log`.
- 2026-08-06: tightened the finite integral theater's theta scale to the
  actual positive norm `||5||_5` of its selected local q-parameter, rather than
  an unrelated demonstration constant. Lean proves positivity and the exact
  identity `||5||_5 = exp(localUnitNormDegreeFor 5 q)`, so the theta packet and
  local degree are now on one explicit scale. The focused check passed with
  zero warnings in `logs/lean/concrete-integral-hodge-qnorm-degree-20260806-070538.log`.
- 2026-08-06: closed the local-scale unit with a fresh production build and
  axiom audit. `lake build LeanFormal` passed at `3832` jobs with zero warnings
  in `logs/lean/build-LeanFormal-concrete-local-scale-20260806-070613.log`,
  and `verification/axiom_audit.lean` passed in
  `logs/lean/axiom-audit-concrete-local-scale-20260806-070613.log`. No new
  `sorryAx` or custom declaration was introduced.
- 2026-08-06: the post-unit custom declaration scan again reports
  `customAxiomDeclarations = 0` in
  `logs/lean/custom-axiom-scan-concrete-local-scale-20260806-070806.log`.
- 2026-08-06: after the two C-layer concrete units, the production axiom audit
  passed with exit code `0` in
  `logs/lean/axiom-audit-concrete-integral-hodge-20260806-070308.log`.
  Sampled declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`; the custom `axiom`/`opaque` scan reports zero declarations in
  `logs/lean/custom-axiom-scan-concrete-integral-hodge-20260806-070309.log`.
  The only production `sorry` remains
  `theorem311_produces_stepXI_contract` in `StepXI/Contract.lean`.
- 2026-08-06: extended `ConcreteIntegralHodgeTheaterExample` with the exact
  logarithmic identity
  `Real.log gaussianFiveThetaQ = Multiplicative.toAdd (localUnitNormDegreeFor 5 q)`
  and the resulting finite theta-packet log-volume formula. The focused module
  build passed with exit code `0` and zero diagnostics in
  `logs/lean/concrete-integral-hodge-log-volume-20260806-071200.log`.
  The complete production aggregate passed at `3832/3832` with zero warnings in
  `logs/lean/build-LeanFormal-concrete-log-volume-20260806-071225.log`.
  The unified post-unit audit is recorded in
  `logs/lean/unified-c-audit-20260806-071320/`: the axiom audit and strict
  boundary both exit `0`, the boundary contains exactly the one permitted
  `sorryAx`, and `check_no_custom_axioms.ps1` reports zero declarations.
- 2026-08-06: added the next C-layer carrier batch: dependent finite
  `HodgeTheaterHistory` composition with a concrete three-step finite history,
  the exact finite cyclic `ZMod l` Tate direction and its kernel/generator
  order, the integer slice of the concrete local Kummer root system, actual
  stable/good/multiplicative reduction-place set bridges, and definitional
  restriction facts for the finite integral F-prime-strip. The aggregate
  passed at `3840/3840` with zero warnings in
  `logs/lean/build-LeanFormal-c-candidate-batch-fix2-20260806-073503.log`, and
  the final unified audit is under
  `logs/lean/unified-c-candidate-audit-20260806-073557/`. The strict boundary
  has exactly the single permitted `theorem311_produces_stepXI_contract`
  `sorryAx`; custom top-level declarations remain zero. These are concrete
  carriers and derived algebraic facts only: the source's distinct histories,
  geometric etale/Frobenioid recognition, stable reduction existence, Tate
  uniformization, and vertical log-Kummer construction remain pending.
- 2026-08-06: closed the completion-characteristic bridge in
  `Foundations/Geometry/TateUniformizationContract.lean`. The adic completion
  now receives the inherited `CharZero` instance from its number field, so the
  curve-indexed Tate-uniformization contract elaborates without adding a
  premise or changing any mathematical field. The complete production build
  passed at `3843/3843` with zero warnings in
  `logs/lean/build-LeanFormal-c-candidate-batch-fix3-20260806-074413.log`.
  The unified boundary audit passed in
  `logs/lean/axioms-20260806-074714/` and
  `logs/lean/axioms-upstream-foundations-20260806-074743/`: exactly the one
  permitted Theorem 3.11-to-Step XI `sorryAx`, no upstream `sorryAx`, and zero
  custom top-level `axiom`/`opaque` declarations. This closes the current
  carrier batch only; stable-reduction existence, Tate uniformization and
  Galois equivariance, source-faithful Hodge histories/theta-links/log-links,
  and the vertical log-Kummer construction remain C-layer obligations.
- 2026-08-06: added the next source-facing algebraic C-layer batch. In
  `Foundations/Geometry/TateDeckAction.lean`, a base-field algebra
  equivalence acts on algebraic-closure units, fixes the actual q-parameter
  unit, preserves its `q^Z` deck subgroup, and descends to a proved
  multiplicative quotient equivalence. In
  `IUTII/Kummer/ConcreteEtaleKummerBridge.lean`, the exact finite
  `Z/lZ` Tate-direction kernel is connected to the already constructed
  compatible root system at `q=p`: a zero finite label is an l-fold integer
  Kummer exponent, and label one is the actual q carrier. These are proved
  algebraic carriers, not claims of geometric etale descent, Frobenioid
  recognition, Tate uniformization, or a source theta/log-link. The complete
  production build passed at `3845/3845` with zero warnings in
  `logs/lean/build-LeanFormal-c-candidate-batch-fix11-20260806-081532.log`.
  The unified boundary checks passed in
  `logs/lean/axioms-20260806-081625/` and
  `logs/lean/axioms-upstream-foundations-20260806-081649/`: exactly the one
  permitted Theorem 3.11-to-Step XI `sorryAx`, no upstream `sorryAx`, and zero
  custom top-level `axiom`/`opaque` declarations.

- 2026-08-06: completed a roughly 1,000-line bottom-up local Tate/Kummer
  prerequisite batch before adding any higher Hodge-theater or Theorem 3.11
  construction. `Foundations/Geometry/ConcreteTateParameter.lean` proves the
  actual `q=p` element in `Q_p`, strict contraction, canonical q-series
  summability, q-unit nontriviality, and positive-power valuation facts.
  `ConcreteTateKummerPacket.lean` ties the actual integral carrier to the
  compatible root system, proves integer-root additive/zsmul laws, and proves
  the exact finite `Z/lZ` kernel. `ConcreteTateFiniteLevel.lean` constructs
  the quotient by the actual kernel and its additive equivalence with
  `ZMod l`, including representative and multiple-class laws.
  `ConcreteTateDeckQuotient.lean` constructs the actual `q^Z` deck subgroup,
  proves local absolute-Galois invariance, and descends the action to the
  quotient with identity/composition and class laws. Finally,
  `ConcreteTateLocalCarrier.lean` assembles these independently checked
  packets into one carrier.

  The complete production build passed at `3850/3850` with zero warnings in
  `logs/lean/build-concrete-tate-1000-line-batch-fix7-20260806-085213.log`.
  The strict boundary audit passed in
  `logs/lean/axioms-20260806-085308/`: exactly the one permitted
  `LeanFormal.IUT.theorem311_produces_stepXI_contract` `sorryAx`. The upstream
  foundations audit passed in `logs/lean/axioms-upstream-foundations-20260806-085309/`
  with no `sorryAx`, and `check_no_custom_axioms.ps1` reports zero custom
  declarations. This batch still does not prove stable or split-multiplicative
  reduction for an input curve, Tate uniformization with curve points,
  Galois-equivariant point identification, Frobenioid/etale recognition,
  source theta/log links, or any Theorem 3.11 obligation.
- 2026-08-06: completed the next 995-line arithmetic C-layer batch in
  `Foundations/Geometry/TateCurveArithmetic.lean`. The canonical q-series
  Weierstrass equation now has proved exact formulas for `b₂`, `b₄`, `b₆`,
  `b₈`, `c₄`, `c₆`, and `Δ`, together with the standard `c`-relation and
  nondegeneracy equivalences. Strict contraction gives the nonvanishing
  denominators used by every positive q-power; summability is retained as an
  actual complete-field theorem, and norm bounds require an explicit
  summable-norm premise rather than silently assuming absolute convergence.
  Variable-change weights for `c₄` and `Δ`, ellipticity from a nonzero
  discriminant, and the j-invariant invariance are proved from Mathlib's
  Weierstrass API. Explicit good and multiplicative reduction certificates
  carry their own integral/minimal model witnesses and transport to the
  source reduction predicates; the curve-indexed Tate contract transports
  equation invariants and conditional reduction facts to the represented
  local curve. The batch does **not** prove the q-series discriminant is
  nonzero for `q=p`, does not supply a certificate for a chosen arithmetic
  input curve, and does not construct Tate uniformization or its Galois
  equivariance. The standalone module is warning-free in
  `logs/lean/tate-curve-arithmetic-batch-final2.log`; production
  `lake build LeanFormal` passed `3851/3851` in
  `logs/lean/build-tate-arithmetic-batch-20260806-final.log`.
  The production axiom audit in
  `logs/lean/axiom-audit-tate-arithmetic-20260806.log` contains exactly the
  permitted `LeanFormal.IUT.theorem311_produces_stepXI_contract` `sorryAx`;
  the upstream audit has no `sorryAx`, and the custom declaration scan reports
  `customAxiomDeclarations = 0` in
  `logs/lean/custom-axiom-scan-tate-arithmetic-20260806.log`.
- 2026-08-06: completed the next bottom-up p-adic estimate batch in
  `Foundations/Geometry/TateCurvePadicEstimates.lean`. For every prime label
  `l >= 5`, the actual `q = l` in `Q_l` now has proved denominator norm one,
  Lambert-term geometric bounds, finite-shift and finite-`Fin` packet error
  bounds, and strict first-term dominance. The canonical q-series `a₄` and
  `a₆` are proved nonzero by the nonarchimedean principal-term argument; the
  canonical `c₄` has norm one and is a unit. The module also constructs
  explicit integral `PadicInt` witnesses for `q`, the coefficients and all
  positive-index denominators, including the local coefficient packet and
  its audit boundary. These are genuine p-adic estimates, not an assertion
  that the q-series discriminant is nonzero.

  The standalone module passed with zero diagnostics in
  `logs/lean/tate-padic-estimates-batch-20260806-r11.log`. After adding it to
  `LeanFormal/IUT/Project.lean`, the production target passed `3850/3850`
  with zero diagnostics in
  `logs/lean/tate-padic-estimates-project-20260806-r4.log`. The selected
  endpoint axiom audit is
  `logs/lean/tate-padic-estimates-axiom-audit-r2-20260806.log`; every endpoint
  uses only `propext`, `Classical.choice`, and `Quot.sound`. The production
  custom declaration scan is zero in
  `logs/lean/tate-padic-estimates-custom-axiom-scan-20260806.log`. The full
  `LeanFormal` aggregate then passed `3852` jobs in
  `logs/lean/tate-padic-estimates-full-aggregate-20260806.log`.
  Remaining C-layer obligations are unchanged: nonzero canonical
  discriminant, identification with an arithmetic input curve, actual
  stable/split multiplicative reduction, Tate uniformization with points and
  Galois equivariance, and source-faithful theta/log-link data. The sole
  production `sorryAx` remains the explicit Theorem 3.11-to-Step XI contract.
- 2026-08-06: completed the next approximately 1,000-line discriminant batch in
  `Foundations/Geometry/TateCurveDiscriminantEstimates.lean`. The expanded
  canonical discriminant is decomposed as `-a₆` plus four correction terms.
  Each correction is proved to have strictly smaller `p`-adic norm than
  `a₆`; nested non-archimedean estimates then prove the exact discriminant
  norm `||Delta|| = ||q||`, nonvanishing, ellipticity of the canonical
  q-series curve, and the explicit discriminant obligation. An integral
  `PadicInt` discriminant witness is transported to the integral Weierstrass
  presentation; its residue is zero while its generic-fiber image is nonzero,
  and the integral `c₄` remains a unit. General strict-dominance certificates
  and consumer-facing output packets are included for later C-layer modules.
  The standalone batch passed with zero diagnostics in
  `logs/lean/tate-curve-discriminant-batch-20260806-r12.log`; the Project
  target passed in `logs/lean/tate-curve-discriminant-project-20260806-r2.log`;
  the full production build passed `3853/3853` in
  `logs/lean/tate-curve-discriminant-full-20260806.log`. The selected endpoint
  axiom audit is `logs/lean/tate-curve-discriminant-axiom-audit-r2-20260806.log`:
  only `propext`, `Classical.choice`, and `Quot.sound` occur for this batch,
  while the production audit still contains exactly the pre-existing
  Theorem 3.11-to-Step XI `sorryAx`. The module has no custom `axiom`,
  `opaque`, or `sorry` declarations. This closes the canonical q-series
  discriminant obligation only; it still does not identify the curve with a
  separately supplied arithmetic input or construct stable/split reduction,
  Tate uniformization, Galois-equivariant points, or source-faithful theta and
  log links.
