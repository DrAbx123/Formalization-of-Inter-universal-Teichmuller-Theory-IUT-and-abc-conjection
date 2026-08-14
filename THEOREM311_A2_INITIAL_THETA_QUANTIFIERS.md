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

## Append-only checklist record (2026-08-14)

The current A2 boundary has been extracted into
`THEOREM311_A2_SOURCE_COMPLETION_CHECKLIST.md`. It records `interface` for
the source contract/conditional recognition and `pending` for the faithful
universal construction from `InitialThetaArithmeticData`; reusable foundation
results are kept separate from proved A2 closures. This is a documentation-only
update. No Lean verification or axiom audit was run, and the earlier research
entries remain unchanged.

## Append-only implementation note: explicit SourceCompletion stage (2026-08-14)

The A2 implementation now adds
`LeanFormal/IUT/IUTI/InitialTheta/SourceCompletion.lean`. Its
`SourceCompletionSignQuotient` stage carries the actual orbicurves, sign action,
quotient universal witness, finite-etale group data, scalar extensions, place
section, bad-place set, and boundary cusp field-by-field; the constructor
`SourceCompletionSignQuotient.toSourceSignQuotientData` assembles the existing
dependent source record without changing any carrier. `SourceCompletion` then
carries the real Clause A--F records in dependency order and
`SourceCompletion.toSourceNativeInitialThetaData` assembles the endpoint.

The tuple's first entry was corrected at the same time: `fbar` is now a
`SourceFbarExtension` carrying a field, `Algebra`, algebraicity,
algebraic-closedness, and an `AlgEquiv` to `AlgebraicClosure A.F`; it is no
longer an element of the closure. This is an unverified implementation batch;
it proves no universal arithmetic-to-source existence statement.

## Append-only source reading note: Clause (c) representation base (2026-08-14)

A source-text check of IUT I, Definition 3.1(b)-(d), pp. 62-63, resolves the
representation base unambiguously. Clause (c) first uses the outer action
`G_F = Gal(Fbar/F)` on `E_F[l]`; `K` is then the finite Galois kernel field of
that representation. Clause (d) subsequently forms the `K`-side covering and
the rank-one quotient of `E_K[l]`. Therefore the current
`SourceAbsoluteGalois A := AlgebraicClosure A.F ≃ₐ[A.F] AlgebraicClosure A.F`
and the separate `A.K` kernel-field identification preserve the source order;
introducing a new `K`-absolute-Galois carrier at Clause (c) would change the
source contract rather than repair it. This is a source-contract confirmation,
not a construction of the representation or its large-image hypothesis.

## Append-only implementation note: K-side torsion boundary correction (2026-08-14)

The rank-one quotient carrier was corrected to the actual base-changed curve:
`TorsionRankOneQuotientData l (A.curve.baseChange A.K)` and hence its module is
`(A.curve.baseChange A.K).LTorsion l`. The previous generic quotient helper had
been partially generalized but still contained stale arithmetic-parameter
references; those are now removed.

Clause (c) now carries a source-supplied K-side basis, an explicit linear
transport from K-side torsion to the F-side torsion module, and the equality
that transports the K basis to the already supplied F-side representation basis.
Clause (f) binds its boundary quotient basis to that K-side basis and exposes
the transported F-side equality as a theorem. This is an interface correction:
no K/F torsion identification is constructed from arithmetic data, and no cusp
or K-rational descent is claimed. The edit batch remains below the 3000-line
verification threshold, so compilation, warning, and axiom evidence remain
`N/A`.

## Append-only research note: no reusable K/F torsion transport (2026-08-14)

A focused search of `EllipticTorsion.lean` and the current IUT foundations found
no theorem giving a linear equivalence between
`(A.curve.baseChange A.K).LTorsion l` and `A.curve.LTorsion l`, no K-rational
descent of the `E_K[l]` carrier, and no identification of the two algebraic
closures' point sets suitable for the Clause (f) quotient. The reusable results
remain curve-local: each curve gets its own algebraic-closure torsion, Galois
action, continuous representation, and kernel field.

Consequently `SourceClauseC.k_to_f_torsion_transport` remains an explicit
source dependency. It must not be filled by an arbitrary closure equivalence,
`Classical.choice`, or a same-named carrier. This search is a dependency note,
not compilation or completion evidence.

## Append-only source-text cross-check: Definition 3.1 clauses (2026-08-14)

A rereading of IUT I, Definition 3.1(a)-(f), pp. 61-64, confirms the exact
dependency order used by the contract. Clause (a) quantifies stable reduction at
all nonarchimedean places of `F`; Clause (b) locates bad places over
`V_mod^bad`; Clause (c) acts first on `E_F[l]` and defines `K` from the kernel;
Clause (d) then introduces the K-side orbicurves, finite-etale cover, cartesian
and open-subgroup diagrams; Clause (e) requires independent local diagrams at
every selected finite and infinite place; and Clause (f) requires the cusp to
come from the same K-side quotient and its canonical generator up to sign.

The K-side carrier correction therefore fixes only the direction of the torsion
module; it does not close any of the missing diagram, local-model, or
canonical-cusp constructions. No weakened carrier or unrelated proposition was
introduced by this cross-check.

## Append-only implementation note: constructed K/F torsion carrier transport (2026-08-14)

本轮没有把 K-side `LTorsion` 与 F-side `LTorsion` 视为同一类型。新增的
`SourceTorsionTransport.lean` 先由有限扩张 `A.K/A.F` 构造两代数闭包之间的真实
`A.F`-代数等价，再由 Weierstrass affine/projective 点群的实际映射构造闭包点
`AddEquiv`，并限制、升级到实际 `ZMod l`-扭点线性等价。二次 base-change 的曲线
相等通过 `Projective.map_baseChange` 和 scalar-tower algebra map 证明。

因此 `SourceClauseC` 的 K-side basis 由同一 F-side basis 和该 transport 的逆映射
派生，compatibility equality 由线性等价的 `trans`/`symm` 恒等式证明；没有引入
任意 closure equivalence、任意 carrier 选择或 K-rational descent 的假设。
这只收口一个缺失的载体传输依赖，不关闭 Clause (c) 的 rationality、大像、kernel
field，也不关闭 Clause (f) 的真实 quotient/cusp。新增代码尚未统一编译，证据仍为
`N/A`，状态保持 `interface`。

## Append-only verification note: A2 source assembly (2026-08-14)

本批次在超过 1000 行实质编辑后完成了顺序单文件验证。以下 A2 文件均显式
生成 `.olean`、退出码为 0 且无 warning：`SourceDefinition31Quantifiers.lean`、
`SourceCompletion.lean`、`SourceTorsionTransport.lean`、`SourcePlaceSelection.lean`
和 `SourceTorsionRankOneQuotient.lean`。`SourceCompletion.toSourceNativeInitialThetaData`
及其 arithmetic-preserving projection 因此有当前批次的编译证据；它们只消费
一个已经携带全部 source 字段的 completion。

定向 `#print axioms` 结果仅为标准 Lean 基础的
`propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`；A2 目录的 custom
axiom 扫描为 0。该结果不构造任意 arithmetic record 的 source witness，故
`SourceNativeArithmeticToSourceGate` 仍保持 `pending`。总入口编译仍因已有
缺失的 `Foundations/Arithmetic/Radical.olean` 而不能作为全项目证据。

## Append-only arithmetic prelude construction (2026-08-14)

本轮没有停留在“没有可复用结果”的检索层面，而是新增
`SourceArithmeticPrelude.lean`，将 arithmetic record 可忠实推出的公共对象
实际构造出来：规范代数闭包及其 `AlgEquiv`、全量 finite/infinite place
restriction section 及 selected-place equivalence、以及真实 K/F `LTorsion`
线性 transport。`SourceCompletion` 现在显式携带该 prelude，且
`SourceCompletion.ofSourceNative` 使用
`SourceArithmeticPrelude.fromPlaceSection` 复用同一 source `V_section`，
所以这些对象不会在各 clause 中被重复选择或错绑。

该构造没有把任何缺失的原文条件放进结论：`V_mod_bad`、stable reduction、q
parameter、Tate uniformization、large image、kernel-field identification、
finite-etale diagrams、completion-level local models 和 quotient-origin cusp
仍未由 arithmetic record 推出。因本轮实质编辑尚未达到 3000 行，尚未进行统一
编译、零 warning 检查或公理审计；当前状态只能记为 arithmetic prelude
`interface`/待验证，A2 universal gate 仍为 `pending`。

## Append-only verification note: arithmetic prelude and source package (2026-08-14)

本批次在累计实质编辑超过 3000 行后，实际编译并通过且无 Lean warning 的
A2 文件为：`SourceTorsionTransport.lean`、`SourcePlaceSelection.lean`、
`SourceDefinition31Quantifiers.lean`、`SourceArithmeticPrelude.lean`、
`SourceCompletion.lean`、`SourceTorsionRankOneQuotient.lean`。

`SourceArithmeticPrelude` 从任意 arithmetic record 构造真实闭包比较、全量
restriction section、selected finite/infinite partition 和 K/F torsion
transport；`SourceCompletion` 只对已给 source witness 证明这些对象与
`V_section`/selected-place 字段一致。该批次没有从 arithmetic record 构造
真实 orbicurve、稳定约化、Tate comparison、large image、local diagrams 或
cusp origin，因此 universal source gate 仍为 `pending`。尚未执行本批次公理
审计，不能把 package 或全称门标为 `proved`。

## Append-only audit note: A2 batch trust boundary (2026-08-14)

定向 `#print axioms` 检查了 source predicate、completion assembly、arithmetic
gate、arithmetic prelude canonical/from-place 构造、K/F torsion transport 和
rank-one quotient 非零类。所有输出仅含标准基础 `propext`、
`Classical.choice`、`Quot.sound`，没有 `sorryAx`。对 A2 InitialTheta 源目录
运行 `check_no_custom_axioms.ps1` 返回 `customAxiomDeclarations: 0`。

总入口 `Project.lean` 在生成 `Radical.olean` 后仍因已有的
`Foundations/Arithmetic/PadicValuation.olean` 缺失而失败；该缓存问题不属于
A2 本轮代码。故 A2 文件的单文件编译证据成立，但不能声称全项目零 warning；
arithmetic-to-source universal gate 继续保持 `pending`。

## Append-only status closure: arithmetic public primitives (2026-08-14)

本批次把三个不属于 Clause A-F 存在性、但确实由 arithmetic record 构造的公共
对象收口为 `provedKernel`：实际 `AlgebraicClosure A.F` 的
`SourceFbarExtension.canonical`；`NumberFieldPlace.restrictionSection` 的
selected-place equivalence、finite/infinite partition 与 comap 左逆；以及实际
K-side/F-side `LTorsion` 的 `initialThetaKToFTorsionTransport` 与双射性。
这三个 kernel 结论不改变 source package 的 `interface` 状态，也不改变
arithmetic-to-source universal gate 的 `pending` 状态。

## Append-only carrier-binding note (2026-08-14)

`SourceArithmeticPrelude.fbar` 与 `.torsionTransport` 现由 arithmetic record
唯一决定，不再允许通过 prelude 结构字段另行填写；`SourceCompletion` 以真实
`AlgEquiv` 将 source tuple 的 chosen closure 与 canonical prelude closure
绑定，并证明其 base-map compatibility 与 bijectivity。该修正只收紧 carrier
身份，不构造 orbicurve、Clause A-F 或 universal source witness。

## Append-only construction note: singleton odd-place selection (2026-08-14)

新增 `SourcePlaceSelection.singleton A p hodd`，从明确给出的有限处和其奇剩余
特征证明构造 `V_mod_bad = {p}`、非空性及 odd-characteristic 字段；它不声称
曲线在该处坏约化、乘法约化或存在 Tate uniformization，故 Clause B 和
arithmetic-to-source universal gate 仍为 `pending`。

## Append-only gate-consequence construction (2026-08-14)

新增 `SourceArithmeticGateConsequences.lean`，从已给出的
`SourceNativeArithmeticToSourceGate` 实际投影出 source 端必须出现的条件，且每
个投影都保留 native witness 与 `T.arithmetic = A`：

* per-arithmetic `SourceCompletion`/native witness 等价；
* (a) 全部 `F` 非阿基米德处稳定约化、field-of-moduli 和 maximal-solvable；
* (b) 同一坏处集合上的 odd residue characteristic、multiplicative reduction、
  `SourceTateComparisonWitness` 和 `l` 互素；
* (c) 真实扭点有理性、basis、`SL₂` 大像和 kernel-field identification；
* (d) K-side finite-etale cover/group inclusion；
* (e) 每个 selected finite/infinite place 的独立 local source；
* (f) 同一 quotient-origin cusp、`epsilon` 兼容及非零 quotient class。

这些是对 universal gate 的必要条件构造，不是从 arithmetic record 反向制造
source witness；因此没有改变 source contract 的量词，也没有关闭
`InitialThetaArithmeticData → SourceNativeInitialThetaData`。本批次尚未达到
3000 行统一验证门槛，机器证据保持 `N/A`，状态为 gate-consequence
`interface`、arithmetic-to-source `pending`。

## Append-only place-level construction note (2026-08-14)

`SourcePlaceSelection` 现在实际构造坏模处的选定上方有限处：
`selected_bad_place_mem` 给出 `V_bad` 归属，`selected_bad_place_is_finite` 给出
有限性，`selected_bad_place_comap` 证明 restriction section 的 comap 左逆，
并由 `V_bad_nonempty` 得到 `V_bad` 非空。所有结论使用同一个
`V_mod_bijection`，没有把下方处与任意上方 carrier 混用。坏约化、Tate
uniformization 和其 coprimality 仍未由 arithmetic record 推出。

## Append-only construction note: geometric core/place binding (2026-08-14)

新增 `SourceSignQuotientConstruction.lean`。它不把 place 字段留作可独立填写的
重复接口：`SourceSignQuotientGeometricCore` 携带同一 source 几何、sign quotient、
群、scalar extension 与 cusp，`SourcePlaceSelection` 携带实际 restriction
section 及 `V_mod^bad`，构造器将二者绑定为一个 `SourceCompletionSignQuotient`
并投影为 `SourceSignQuotientData`。这只关闭 place 字段的结构性绑定路线，仍不
构造 geometric core 或从 arithmetic record 关闭 A2 universal gate。本批次未达
3000 行验证阈值，新增文件的编译和审计证据保持 `N/A`。

## Append-only staged clause-binding verification (2026-08-15)

`SourceClauseConstructors.lean` 已在修正 sort 与 dependent-index 问题后单文件
编译通过：

`lake env lean LeanFormal/IUT/IUTI/InitialTheta/SourceClauseConstructors.lean -o .lake/build/lib/lean/LeanFormal/IUT/IUTI/InitialTheta/SourceClauseConstructors.olean`

命令退出码为 `0` 且无 Lean 输出，因而该文件没有 warning。该结果证明的是从
显式 source objects/witnesses 到 Clause A-F 记录的忠实绑定和 `sourceData` 组装，
不是从任意 `InitialThetaArithmeticData` 产生 source record；真实 sign quotient、
reduction、Tate uniformization、kernel-field descent、local diagrams 与 cusp
origin 仍是未闭合依赖，universal gate 仍为 `pending`。本次尚未执行公理审计，
不能据此声称 A2 package 或全项目已完成。

## Append-only current checklist marking and verification (2026-08-15)

本轮根据 A2 checklist 的实际证据补记状态。修复
`SourcePlaceSelection.selected_bad_place_mem` 使用显式 `Equiv.left_inv` 后，
以下文件逐个编译，均退出码 `0` 且无 Lean 输出：

* `SourcePlaceSelection.lean`
* `SourceTorsionTransport.lean`
* `SourceArithmeticPrelude.lean`
* `SourceDefinition31Quantifiers.lean`
* `SourceCompletion.lean`
* `SourceSignQuotientConstruction.lean`
* `SourceClauseConstructors.lean`
* `SourceTorsionRankOneQuotient.lean`

因此本轮只把 arithmetic kernel、`SourceCompletion` 到 native 的 source-witness
组装、geometric-core/place 绑定和 Clause A--F source-facing constructors 标为
已验证；所有这些声明仍消费显式 source objects/witnesses。定向
`#print axioms`（`verification/a2_source_axiom_audit.lean`）只报告
`propext`、`Classical.choice`、`Quot.sound`；
`check_no_custom_axioms.ps1 -SourceRoot LeanFormal/IUT/IUTI/InitialTheta`
报告 `customAxiomDeclarations: 0`，没有 `sorryAx`。`InitialThetaArithmeticData →
SourceCompletion` 及 `InitialThetaArithmeticData → SourceNativeInitialThetaData`
仍为 `pending`，因为 reduction、真实 orbicurve/group、Tate、local diagrams、
kernel-field descent 和 cusp origin 尚未由 arithmetic data 构造。

按 A2 范围移除了只从已假设 universal gate 投影必要条件的
`SourceArithmeticGateConsequences.lean` 及其 `Project.lean` 导入；该文件不再作为
A2 进度或证明路线。
