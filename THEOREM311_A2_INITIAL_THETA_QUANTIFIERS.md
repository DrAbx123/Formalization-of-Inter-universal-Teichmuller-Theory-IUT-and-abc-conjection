# A2 initial Theta-data quantifier note

Status date: 2026-08-13

## Source boundary

The source is IUT I, Definition 3.1(a)-(f), continuous text lines 3123-3280
of `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory I.txt`,
printed pages 61-64. The fixed collection is

`(Fbar/F, X_{F,l}, C_K, V, V_mod^bad, epsilon)`.

The definition says that a collection is called initial Theta-data when it
satisfies all six clauses. It does not quantify over the smaller project
record `InitialThetaArithmeticData` and it does not assert that every such
record has a source realization.

## Lean declarations

The machine-readable contract is
`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean`.

Reusable source declarations are:

- `SourceInitialThetaCandidate`: the tuple carrier and place maps;
- `ClauseA`, `ClauseB`, `ClauseC`, `ClauseD`, `ClauseE`, `ClauseF`: dependent
  records for the six source clauses;
- `SourceInitialThetaData`: the tuple together with all six clauses;
- `InitialThetaDataConclusion`: the recoverable source conclusion;
- `initialThetaData_conclusion : forall S, InitialThetaDataConclusion S`:
  conditional recognition for an already qualified source tuple.

The new A2 contract also records an explicit bridge from the encoded `V`
carrier to an actual `Set (NumberFieldPlace K)`. This bridge is an interface;
it is not constructed by the file.

## Quantifier order

The source-facing recognition is universally quantified over every supplied
`SourceInitialThetaData`. The dependent clause assembly keeps the order

`D, ClauseA, ClauseB, ClauseC, ClauseD, ClauseE, ClauseF`.

The existing source records retain the local universal binders, including all
finite places over `F`, bad-place hypotheses over `V_mod^bad`, local place
indices, and cusp localization. No `Nonempty` proposition is used as a
replacement for a clause object.

## Open gates

The following propositions are deliberately only gates:

`InitialThetaArithmeticToSourceGate` requires
`forall A : InitialThetaArithmeticData l, exists S : SourceInitialThetaData l,
S.candidate.arithmetic = A`.

`InitialThetaArithmeticToFaithfulSourceGate` additionally requires the literal
selected-place subset bridge for `V subset V(K)`.

Both remain `pending`. Stable/multiplicative reduction, Tate
uniformization q-parameters, torsion/Galois large-image data, genuine
hyperbolic orbicurves and profinite etale exact sequences, local sections, and
the cusp from a nonzero quotient must be constructed from their cited source
objects before either gate can be closed. Generic carriers, arbitrary reals,
`Classical.choice`, finite examples, and same-named fields do not close them.

## Verification state

This note and the audit entry record the implementation boundary only. The new
Lean contract has not yet been compiled or audited in this edit batch because
the project rule requires a batch of at least 3000 substantive edited lines
before compilation, warning checks, and axiom audits. Until that batch is
reached, A2 remains `interface` for conditional recognition and `pending` for
arithmetic-to-source construction.

## Append-only research log: source-boundary correction pass (2026-08-14)

The current Lean edit contains the following source-faithful corrections; this
entry records the implementation, not a compilation claim.

* **Full `V(F)^non` carrier.**  `V_F_nonarchimedean` is now the full set of
  finite places of `A.F` (`Set.univ`), with its specification theorem.  The
  selected-place finite subset remains a separate derived carrier.  Thus the
  stable-reduction quantifier is not restricted to the downward image of `V`.
  See `SourceDefinition31Quantifiers.lean:516-526` and the Clause A field at
  `:630`.
* **No generic `sSup` construction.**  The earlier generic maximal-extension
  construction was removed.  Clause A now receives an actual intermediate
  field `IntermediateField A.Fmod A.F` and proves its finite-dimensional,
  Galois, solvable, and source-restricted maximal-containment properties via
  `isFiniteSolvableGaloisSubextension`.  See `:634-641`.
* **Clause D dependent cover.**  The K-side cover is indexed by the actual
  `S.xK` and `S.cK` orbicurves, and its map is required to equal the actual
  sign-quotient morphism.  The quotient action, invariant morphism, quotient
  witness, scalar-extension comparison, and profinite group embeddings are
  carried in the same dependent record.  See `:802-818` and the subsequent
  `SourceClauseD` fields.
* **Canonical quotient-boundary origin.**  Clause F now uses
  `TorsionQuotientBoundaryOrigin l A S.cK`, ties its rank-one quotient basis to
  the Clause C torsion basis, identifies its cusp with the tuple's `epsilon`,
  and records the canonical nonzero-class-to-cusp map.  This removes the old
  unrelated witness `∃ q : A.K, q ≠ 0`.  See `:1237-1289`.
* **Dependent tuple predicate.**  `SourceInitialThetaTuple` explicitly carries
  `xF`, `cK`, `V`, `V_mod_bad`, and `epsilon`, together with equalities tying
  them to one `SourceSignQuotientData` source.  The endpoint predicate
  `SourceNativeInitialThetaPredicate` is a dependent existential over clauses
  (a)--(f), while `SourceNativeInitialThetaRecognition` only recognizes an
  already supplied source datum.  See `:1302-1424`.

### Current compilation blockage

This pass has not yet been compiled.  Consequently the declarations above are
not recorded as `proved`, and the remaining blocker is the required Lean
type-check/closure of the newly dependent source graph: in particular the
scalar-extension/pseudofunctor structures, the local completion records and
their exact-sequence embeddings, the dependent cover equalities, and the
`TorsionQuotientBoundaryOrigin` interface must all elaborate together before
the A2 file can be checked for zero warnings and audited for `sorryAx` or
custom axioms.  The audit statuses therefore remain `interface` for
conditional recognition and `pending` for arithmetic-to-source construction.

## Append-only correction: current A2 implementation pass (2026-08-13)

The declaration inventory above describes the previous implementation and is
retained as historical record.  The current unverified rewrite is in
`LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean` (537
lines at this update).  Its source-facing carriers now include the actual
`AlgebraicClosure A.F`, the absolute-Galois automorphism type, the existing
`NumberFieldPlace`/restriction-section types, `PuncturedEllipticCurve`, the
project orbicurve/sign-action/quotient-witness types, finite-etale covers,
profinite exact-sequence data, Tate comparison data, and boundary cusps.  The
six dependent records are currently named `SourceClauseA` through
`SourceClauseF`, and their dependent assembly is
`SourceNativeInitialThetaData`.

This pass does not yet establish the Definition 3.1 input quantifier.  In
particular, the following are recorded as concrete proof or construction
gates, not as fulfilled interfaces:

1. `SourceClauseD` still refers to `Iut.SignQuotientOrbicurveData`, which is
   not a declaration in the main project foundation.  A2 must provide a
   definition built from the actual sign action, quotient witness, covers, and
   exact sequences (or remove the reference) before Clause (d) can be used.
2. The local fields in `SourceClauseE` currently reuse the global exact
   sequences.  They do not yet construct the completion-level local
   orbicurves, groups, embeddings, and base-change diagrams required by the
   printed clause.
3. `SourceClauseF.nonzero_quotient_origin` is presently only
   `∃ q : A.K, q ≠ 0`; this is not the source quotient `Q` and therefore does
   not prove the cusp's stated origin.  The actual quotient object and its
   nonzero element must be constructed first.
4. The fixed six-tuple `(Fbar/F, X_{F,l}, C_K, V, V_mod^bad, epsilon)` is not
   yet represented by one source tuple.  `V`, `V_mod^bad`, and `epsilon` must
   be explicit fields with their source types and dependencies; deriving them
   from `SourceSelectedPlaces A` or re-creating a cusp in Clause (f) is not
   sufficient.
5. `SourceNativeInitialThetaQuantifier` currently proves only the structural
   assembly of already supplied clause witnesses.  It is not the endpoint
   predicate "this supplied six-tuple is initial Theta-data."  A source
   predicate over the explicit tuple, together with a proved equivalence to
   the dependent structure, is still required.
6. Several arithmetic, algebraicity/Galois, coprimality, and continuity
   assumptions are duplicated as fields although corresponding foundation
   results are intended to supply them.  Each duplicate must be replaced by a
   projection of an actually proved theorem, or retained only if the printed
   source clause independently requires it.
7. The current `image_contains_SL2` expression uses a subgroup map form that
   has not been type-checked; the intended source subgroup is the actual
   `Subgroup.map Matrix.SpecialLinearGroup.toGL (⊤ : Subgroup ...)`.
8. The locally introduced scalar-extension and orbicurve-morphism structures
   have not been type-checked against the project `SchemeOverField`,
   `EtaleStackOverField`, and pseudofunctor definitions.  No theorem depending
   on those structures is therefore marked proved.

## Append-only correction: Clause E local-source rewrite (2026-08-13)

The unverified A2 rewrite now gives Clause (e) an independent local source
record for each selected place. `SourceFiniteLocalSource` uses the actual
finite-place completion `NumberFieldFinitePlace.Completion w`, while
`SourceInfiniteLocalSource` uses `NumberField.InfinitePlace.Completion w`.
Both records carry a local curve explicitly identified with the actual base
change of `A.curve`, scalar-extended local `X` and `C` orbicurves, an actual
sign action and quotient witness, independent local profinite fundamental
groups with their own exact sequences, and local `X -> C` inclusion data.
Each local exact sequence is connected to the corresponding `K` sequence only
through an explicit `ProfiniteFundamentalExactSequenceEmbedding`; the old
Clause E fields that simply returned the global `E.x_groups`/`E.c_groups`
inclusion have been removed. `selectedFinitePlace` and
`selectedInfinitePlace` eliminate impossible constructor cases from the actual
`NumberFieldPlace.IsFinite`/`IsInfinite` proofs. The edit is not compiled in
this batch, so these declarations remain an implementation gate rather than
completion evidence.

The status remains `interface` for the conditional dependent assembly and
`pending` for source construction from the arithmetic record.  No Lean
compilation, warning check, `#print axioms`, or `sorryAx`/custom-axiom audit
has been run for this rewrite.  The 3000-substantive-line batch threshold has
not been reached, and this note must not be read as completion evidence.

## Append-only implementation note: tuple and endpoint pass (2026-08-13)

The shared Lean file now carries the three tuple entries that were previously
implicit: `SourceSignQuotientData.V`, `V_mod_bad`, and `epsilon`. `V` is tied
to an actual `NumberFieldPlace.RestrictionSection` by `V_eq_section`, and the
lower-place bijection and its comap compatibility are fields of the same
source tuple. Clause (b), (e), and (f) are being migrated to these dependent
fields; no arithmetic-level re-creation of `V` is intended.

The endpoint declarations now distinguish the source predicate
`SourceNativeInitialThetaPredicate` (a dependent existential over the full
six clause records) from the packaging theorem
`SourceNativeInitialThetaQuantifier`. The proved equivalence to
`SourceNativeInitialThetaExists` is only an existential rearrangement; it is
not an existence result from `InitialThetaArithmeticData`.

This pass is unverified and remains `pending` until Clause (e) local data and
Clause (f)'s Definition 2.1 quotient-origin witness have actual compiled
proofs.

## Append-only research note: Clause F torsion quotient construction (2026-08-14)

The project search found no existing theorem identifying the current
`PuncturedEllipticCurve.LTorsion l` carrier with `E_K[l]`, and no theorem
constructing an `OrbicurveBoundaryCusp` from a torsion quotient.  The printed
source is explicit: IUT I, Definition 3.1(c) uses a rank-one quotient
`E_K[l] -> Q ~= Z/lZ`, and the associated cusp uses a canonical generator of
`Q` up to sign (see the local corpus text for IUT I, pp. 3--4 and the Alien
Copies discussion around p. 59).  Therefore a nonzero element of `A.K` is not
a valid replacement.

An independent Lean file,
`LeanFormal/IUT/IUTI/InitialTheta/SourceTorsionRankOneQuotient.lean`, now
constructs the strongest currently justified algebraic object: from an actual
`A.curve.LTorsion l` and an explicit Clause-C-style rank-two torsion basis it
defines the first-coordinate `ZMod l`-linear surjection, its kernel quotient,
the quotient linear equivalence with `ZMod l`, and a distinguished quotient
class proved nonzero.  This is a genuine algebraic-closure torsion quotient;
the file deliberately does not label it `E_K[l]`, attach it to `A.K`, or claim
cusp origin.  A K-rational descent theorem and a boundary comparison map are
still required before Clause F can use the paper's `Q`/`epsilon` statement.

## Append-only correction: full `V(F)^non` quantifier (2026-08-14)

The previous implementation pass incorrectly used `V_F_non`, the downward
image of selected finite places in `V ⊆ V(K)`, as the carrier of Clause (a)'s
stable-reduction quantifier.  IUT I §0 defines `V(F)^non` to be the full set of
nonarchimedean valuations of `F`, and Definition 3.1(b) requires stable
reduction at every such place.  The production file therefore keeps
`V_F_non` only as the selected-place image and introduces
`V_F_nonarchimedean A = Set.univ`; `SourceClauseA.stable_reduction_nonarchimedean`
now quantifies over every `NumberField.FinitePlace A.F`.  The same pass adds the
source-derived `V_mod_good`, `V_F_bad`, and `V_F_good` partitions with their
cover/disjointness specifications.  This is a source-notation correction, not
an existence result.  No compilation or axiom audit has been run in this edit
batch; A2 remains `interface` for conditional recognition and `pending` for
arithmetic-to-source construction.

## Append-only implementation note: explicit recognition and construction gate (2026-08-14)

The current quantifier file now distinguishes two propositions with different
logical roles:

* `SourceNativeInitialThetaRecognition l` is the paper-facing conditional
  recognition statement. Its proved theorem
  `sourceNativeInitialThetaRecognition` has the exact universal binder
  `forall T : SourceNativeInitialThetaData l`; it only packages the six clause
  witnesses already carried by `T` into `SourceNativeInitialThetaPredicate`.
* `SourceNativeArithmeticToSourceGate l` is a separate, explicitly unproved
  project construction gate. Its type is
  `forall A : InitialThetaArithmeticData l, exists T : SourceNativeInitialThetaData l,
  T.arithmetic = A`. The equality prevents a witness for a different arithmetic
  datum from being silently reused. The accompanying theorem
  `sourceNativeArithmeticToSourceGate_spec` only specializes an assumed gate;
  it does not prove the gate.

The source text fixes `F_sol` as an intermediate field `F_mod subseteq F`;
accordingly `SourceClauseA.maximal_solvable_extension` is carried as
`IntermediateField A.Fmod A.F`, with explicit finite-dimensional, Galois,
solvability, and maximal-containment fields. No `sSup` or generic maximal
extension constructor remains. This is a source contract, not an existence
proof.

This edit batch is still unverified: the quantifier file has not been compiled,
and no new warning, axiom, or `sorryAx` audit has been run. The recognition
interface remains `interface`; the arithmetic-to-source gate remains `pending`.

## Append-only correction: solvable maximality binder (2026-08-14)

The maximality field was tightened to match the phrase "maximal solvable
extension" proportionally. It now quantifies only over
`E : IntermediateField A.Fmod A.F` satisfying the same
`isFiniteSolvableGaloisSubextension E` predicate, and concludes
`E <= maximal_solvable_extension`. The earlier broader finite-plus-Galois
binder was stronger than the source wording and has been removed. This is an
unverified interface edit; no compilation or audit was run.
