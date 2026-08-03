# Mochizuki corpus dependency layers

This is the first, source-backed dependency map for the formalization. It is
not a claim that every bibliography edge has been reconstructed. The raw
corpus, extracted text, page manifest, hashes, and candidate edges are kept in
this directory.

## Evidence used

- `pages.csv` records the eight author-site entry pages and their download
  status.
- `pdfs.csv` records 263 unique PDF links, including one confirmed external
  404 and 262 local files with SHA-256 hashes.
- `documents.csv` records PDF page counts and extracted text sizes.
- `citation_edges.tsv` contains 478 resolved reference-label edges. Each edge
  retains the source file, target file, label, and source line number.
- `unresolved_reference_labels.tsv` records 112 labels that still need title
  resolution (for example older numbered bibliography entries).
- `reference_snippets.tsv` keeps the original bibliography lines used for
  review. The automated edges are candidates, not proof of dependency.

The strongest explicit reading-order evidence is in
`text/Tan --- Introduction to inter-universal Teichmuller theory (slides).txt`,
lines 10--18: treat anabelian results and Frobenioids as prerequisites, read
Sections 1--2 of `EtTh`, read IUT I/II for definitions, then read IUT III
carefully; IUT IV Section 1 can be read alongside IUT III. The bibliography in
`text/2020-11 Classical roots of IUT.txt`, lines 559--585, names the four IUT
papers and the `Pano`/`Alien` expositions.

## Bottom-up layers

| layer | source family | reason for placement | planned Lean area |
|---|---|---|---|
| L0 | ordinary algebra, ordered fields, number fields, elliptic curves, p-adic and log geometry | mathematical foundations used by every later object | `LeanFormal/IUT/Foundations` |
| L1 | anabelian geometry of hyperbolic curves, anabelioids, p-adic Teichmuller theory, log schemes | supplies the Galois/category language used by Frobenioids and Hodge theaters | `IUTI/Anabelian` and `Foundations/Geometry` |
| L2 | `The Geometry of Frobenioids I/II`, `The Etale Theta Function and its Frobenioid-theoretic Manifestations` | Tan's slides identify `EtTh` Sections 1--2 as the basis of IUT; `Alien` cites `FrdI`, `FrdII`, and `EtTh` together | `IUTII/Frobenioid`, `IUTII/Theta` |
| L3 | Hodge-Arakelov theory, theta convolution, arithmetic elliptic curves in general position | supplies the theta data, Gaussian evaluations, and elliptic-curve arithmetic used in IUT I/II | `IUTI/InitialTheta`, `IUTII/Theta`, `Foundations/Arithmetic` |
| L4 | IUT I: Construction; IUT II: Hodge-Arakelov-theoretic evaluation | constructs Hodge theaters, prime strips, theta data, and Kummer infrastructure | `IUTI`, `IUTII` |
| L5 | IUT III: Canonical splittings of the log-theta-lattice | constructs the multiradial output and states Ind1--Ind3 | `IUTIII/Theorem311` |
| L6 | IUT III, Proof of Corollary 3.12, Steps (xi-a)--(xi-g) | the IPL/SHE/APT/hull/normalization/log-volume wall that must be formalized before the conclusion is justified | `IUTIII/Corollary312/StepXI` |
| L7 | IUT IV: Log-volume computations and downstream estimates | depends on the Corollary 3.12 comparison; it cannot repair an earlier missing compatibility proof | `IUTIV/Estimates` |
| E | `Pano`, `Alien`, `Essential Logical Structure`, lecture slides, later notes | explanations and diagnostics; useful for terminology and cross-checking but not prerequisites by themselves | `Audit/Expositions` and `Audit/Sources` |

## Lean lower-layer checkpoint (2026-08-03)

The current production project has an independently compiled L0/L2/L3
checkpoint. `Foundations/Arithmetic/Radical`, `PrimitiveAdditive`,
`PrimeIntervals`, and `PrimeLabels` establish the standard natural-number
radical, primitive additive-triple, and finite prime-label arithmetic used by
the later ABC statement and prime-strip indices. `Foundations/Geometry` gives
the concrete Mathlib Weierstrass model and punctured carrier. The finite
determinant/log module proves the ordinary algebra behind tensor
normalization and finite log-volume comparisons. The Kummer submodules under
`IUTII/Kummer` now contain explicit polynomial/root carriers, compatible
factorial root chains, unit-valued classes, root ratios, and a generic
upper-semi log correspondence.

`Foundations/Arithmetic/NormLog` is the shared L0 norm/log kernel used by the
local p-adic unit carrier. It proves the unit norm followed by `Real.log` is a
`MonoidHom` into `Multiplicative Real`; the p-adic file now contains only the
field instantiation and the IUT-specific carrier record.

`Foundations/Arithmetic/PadicValuation` fixes the natural-number valuation
conventions at L0: prime self-value, multiplication and power laws, prime
support, and the `p^k | n` characterization are direct Mathlib theorems. This
is shared standard arithmetic for the ABC and local-place layers, not a
source-level IUT comparison.

`Foundations/NumberField/FinitePlaces` and `Places` now implement the L0
number-field-place carrier needed by IUT I Definition 3.1. A Mathlib finite
place is recovered from its canonical height-one prime; its residue quotient
is finite, its ring characteristic is prime and positive, and contraction of
the prime defines a restriction map that is transitive in a number-field
tower. Infinite places use Mathlib's embedding-composition restriction, and
the combined finite/infinite carrier is transitive as well.

The restriction map is also now proved surjective on both kinds of places.
Finite-place surjectivity is obtained from Going-Up for the integral extension
of rings of integers; infinite-place surjectivity is Mathlib's extension of
complex embeddings. Choosing one extension of every lower place gives a
noncanonical `RestrictionSection`. Its selected image is proved equivalent,
via restriction, to the full lower-place carrier. This constructs the set
shape of IUT's `V`, but not the additional `V_mod^bad` subset or its reduction
conditions.

`Foundations/NumberField/FinitePlaceExtension` supplies the local-field map
behind restriction. The upper height-one prime is proved to lie over its
contraction, Mathlib's ramification theorem gives `v(x)^e = w(algebraMap x)`,
and uniform continuity extends the dense valued-field embedding to a
continuous injective ring homomorphism between the actual adic completions.
Its formula on base-field elements is proved. Continuity of the two completed
valuations and density of the global field extend the ramification formula to
every completed element. The map therefore restricts to an injective local
homomorphism between the completed valuation rings and induces an injective
residue-field map commuting with the two quotient residue maps.

`Foundations/Geometry/LocalReduction` supplies the next L0 curve kernel.
Mathlib's reduction classes on minimal Weierstrass equations are lifted to
presentation-independent predicates, and their invariance under variable
changes and the chosen minimal model is proved. At a number-field finite
place, these predicates are instantiated on the actual adic completion and
its valuation ring. Split multiplicative reduction implies multiplicative
reduction, hence stable reduction. This does not prove that the IUT input
curve has any of these properties at a specified place.

`Foundations/Geometry/ReductionBaseChange` proves the compatibility layer. A
commuting coefficient-ring/field square maps integral Weierstrass models.
Integral equations with discriminant valuation one or unit `c4` are proved
minimal directly from Mathlib's definition. Good and multiplicative reduction
therefore pass from `k_v` to `K_w`. The chosen integral models and reduced
curves commute with the induced residue-field map; the quadratic tangent-cone
polynomial maps accordingly, so splitting and split multiplicative reduction
are preserved. These are conditional preservation theorems and do not prove
that the specified IUT curve has the lower reduction property.

`Foundations/NumberField/LocalQParameter` isolates the valuation-theoretic
part of a local q-parameter. Every completed finite place contains a nonzero
element of valuation below one, obtained from an irreducible element of its
completed DVR; its discrete order is positive and positive powers remain in
the same class. This is explicitly a `FinitePlaceQCandidate`, not a Tate
parameter of a curve. Mathlib 4.32.2 has elliptic reduction classes but no
Tate-curve uniformization theorem, so the curve identification and Galois
equivariance remain pending.

`Foundations/Geometry/EllipticTorsion` constructs the actual closure-valued
torsion group and absolute-Galois action required by Definition 3.1(c). Point
stabilizers are proved Krull-open. Given a genuine linear equivalence
`(ZMod l)^2 ~= E[l]`, the matrix representation is proved continuous, and its
kernel fixed field is constructed and proved finite Galois; over a number
field it is again a number field. The rank-two basis theorem itself, the
rationality of all six-torsion points, and the image-containing-`SL(2)`
hypothesis remain outside the proved column.

This does not yet move L3/L4 selected-place data into the proved column. The
next lower dependencies are actual stable/split multiplicative reduction
hypotheses for the IUT input, a proof that the local q-candidate gives the
Tate uniformization/parameter of that same curve, and proofs that these
constructions commute with the chosen field restrictions. Sets named
`selected`, `bad`, or `good` are not accepted before they are derived from
this common curve-level data.

The checkpoint is recorded by
`logs/lean/serial-20260803-053739/summary.json` (`59/59` modules) and the
aggregate log `logs/lean/aggregate-20260803-060943.stdout.log` (`3145` jobs).
The trust audit uses only Lean/Mathlib standard axioms for these kernels. The
checkpoint still does **not** construct the source's etale fundamental groups,
Frobenioid prime strips, anabelian reconstruction, holomorphic hull, or the
Theorem 3.11/Step-XI compatibility wall. Those remain higher layers and may
not be inferred from the existence of these lower carriers.

The local-reduction extension is recorded separately by
`logs/lean/serial-20260803-070913/summary.json` (`4/4` targeted modules),
`logs/lean/aggregate-20260803-071039.stdout.log` (`3649` jobs), and
`logs/lean/axioms-20260803-071133/axiom_audit.stdout.log`. Its sampled
theorems use only Lean/Mathlib standard axioms; the production boundary still
contains exactly the pre-existing Step-XI `sorryAx`.

The local q-parameter valuation extension is recorded by
`logs/lean/serial-20260803-072311/summary.json` (`5/5` targeted modules),
`logs/lean/aggregate-20260803-072446.stdout.log` (`3650` jobs), and
`logs/lean/axioms-20260803-072536/axiom_audit.stdout.log`. Its existence and
positive-order samples use only Lean/Mathlib standard axioms; the Tate
uniformization obligation is not represented by a proof field.

The elliptic-torsion/Galois extension is recorded by
`logs/lean/serial-20260803-073457/summary.json` (`4/4` targeted modules),
`logs/lean/aggregate-20260803-073611.stdout.log` (`3652` jobs), and
`logs/lean/axioms-20260803-073701/axiom_audit.stdout.log`. The sampled action,
topological, matrix, continuity, and fixed-field theorems use only
Lean/Mathlib standard axioms.

The place-section extension is recorded by
`logs/lean/serial-20260803-074345/summary.json` (`4/4` targeted modules),
`logs/lean/aggregate-20260803-074502.stdout.log` (`3652` jobs), and
`logs/lean/axioms-20260803-074605/axiom_audit.stdout.log`. Lying-over and the
selected-image equivalence use only Lean/Mathlib standard axioms.

The finite-place completion and reduction-base-change extension is recorded by
`logs/lean/serial-20260803-090015/summary.json` (`7/7` targeted modules),
`logs/lean/run-20260803-090222.stdout.log` (`3655` jobs), and
`logs/lean/axioms-20260803-090331/axiom_audit.stdout.log`. The ramification,
continuity, completed valuation, local valuation-ring/residue-field maps,
integral/minimal model base change, reduction commutation, and all three
reduction-preservation samples use only Lean/Mathlib standard axioms. The
production boundary remains the same single Step-XI `sorryAx`, and the custom
declaration count remains zero in
`logs/lean/custom-axiom-20260803-090331.log`.

## Rules for turning a layer into Lean

1. A layer may import only lower layers, except the audit/exposition layer,
   which is read-only evidence.
2. A definition is accepted as a mathematical object only when its carrier,
   operations, and laws are inherited from standard mathematics or are
   constructed from lower-layer objects. A record with fields named after a
   paper's terms is an obligation contract, not an IUT definition.
3. Every theorem is checked with `#print axioms`; `sorryAx` is allowed only in
   explicitly named unfinished targets. Theorem 3.11 -> Corollary 3.12 is the
   current wall target.
4. Candidate citation edges are used to choose reading order, then each new
   Lean module records the source PDF and page/section that motivated it.
