# M1: Typed Hodge-Theater Source

> **Status correction (2026-07-20).** This document describes the legacy M1
> finite/type-safety model, not completion of the paper-level M1 milestone.
> The authoritative status is the clause ledger in
> `Iut/SourceTrace/M1M3PaperLedger.lean`.

Baseline provenance: M0 is commit `6852a45a`. M1 keeps only the reproducibility
surface needed here: the existing Lake project, the Stage 1 dependency audit,
the blueprint declaration check, and the paper PDF build.

## Boundary

`InitialThetaData` now carries a mod-`l` absolute Galois representation, its
kernel-field condition, `SL2` image containment, and positive bad-place
q-parameter orders prime to `l`. The reconstruction now also ties the
representation to a basis of the actual elliptic `l`-torsion and its Galois
action, requires this Krull-to-finite representation to be continuous,
identifies embedded `K` with the fixed field of the representation
kernel, derives residue characteristics from residue fields, and states stable
reduction over completed local fields using actual local minimal equations.
The resulting good and multiplicative classifications are proved invariant
under Weierstrass coordinate changes, passage to Mathlib's chosen minimal
model, and coordinate change followed by scalar extension. At every `F`-place
above the bad moduli locus, and at each bad selected `K`-place, `q` is now
an actual nonzero contracting element of the adic completion with a Tate
uniformization of the geometric elliptic-curve point group that is equivariant
for the local absolute Galois action; its positive order is derived from the
discrete valuation exponent rather than stored. The analytic/topological
realization of this group-level uniformization remains open.

The source closure now includes the cited Etale Theta Section 2 construction.
`EtaleThetaQuotient` constructs the lower-central theta quotient, its
exponent-`l` quotient, the descended elliptic quotient, and the theta center.
`EtaleThetaCovers` links the original and arithmetic-theta exact sequences,
the cuspidal exact sequence, the Lagrangian quotient, Proposition 2.2
eigenspace splitting, and the theta-root subgroup defined from the chosen
Galois splitting. The theta-root stack interface also records Proposition
2.2(iii)'s normalizing order-two lift, unique admissible coset, conjugation
action, and generation statement. The continuous profinite `Z/lZ` quotient supplies the
derived open kernel and first-isomorphism theorem. `Orbicurve` supplies genuine
strong-transformation morphisms of etale stacks. Representable morphism
properties are tested by full bicategorical pullback squares against every
scheme-valued point, with actual Mathlib finite, etale, and open-immersion
predicates on the resulting scheme maps. The finite-etale cover category of an
orbicurve therefore has objects that literally map to that represented stack;
its hom-sets are identified with actual stack morphisms over the target and its
chosen Galois fiber functor is naturally identified with the corresponding
geometric fibers. A canonical orbicurve
signature now belongs to the represented stack itself; a hyperbolic-geometry
certificate exposes that invariant, and Lean proves that two wrappers of the
same stack cannot advertise incompatible genus, stacky orders, or cusp count.
The source types `(1,1)`, `(1,l-tors)`, theta-root, arrowed, and bad-local
`Z/lZ` refinements are witnessed by their actual scheme, quotient, cover, and
theta constructions rather than free labels. `Orbicurve` also supplies a coherent `C2` action as a
pseudofunctor, quotient-map invariance by an invertible modification, and
open/exact morphisms of profinite groups. `TypeOneLTorsionStackRealization`
contains the cover and sign-quotient stacks and identifies the cover's
arithmetic fundamental group with the profinite group derived from the open
Lagrangian kernel. Its cover square now carries the full bicategorical
pullback universal property. Both the base sign quotient and this cover sign
quotient now carry coherent invariant maps and the bicategorical quotient
universal property: invariant maps factor through the quotient, compatible
2-cells lift, and equality is detected after precomposition. Derivation of the
specified stacks and morphisms as algebraic finite-etale orbicurve covers
remains open.

`OrbicurvePullback` defines the actual restriction-of-scalars functor
`Sch/K -> Sch/F`, scalar extension of stacks by pseudofunctor equivalence, and
scalar extension of orbicurve morphisms by an invertible modification whose
components and naturality cells are the restricted original morphism. Scalar
extension transports the represented stack together with genus, stacky
orders, and cusp count, so its target signature is a theorem rather than a
caller-supplied equality.
`TwoPullbackWitness` encodes essential
surjectivity, lifting of every compatible cone 2-cell, and faithfulness, hence
the full pseudo-cone universal property.

`SourceInitialThetaCore` is the new aggregate path. It constructs the
once-punctured curve as the spectrum of the stored Weierstrass equation's
affine coordinate ring. Its puncture is the origin, and the chosen ambient
compactification identifies the complement of its closed origin section with
that actual affine scheme. The `X_F` stack
is bicategorically equivalent to the scheme's representable Yoneda-style
pseudofunctor, so pullback, identity, and composition coherence are intrinsic,
and its coherent sign
action is identified with the coordinate-induced elliptic-negation scheme map,
whose square is proved to be the identity. The aggregate also includes
stable-reduction and torsion predicates, a concrete `j`-generated
field-of-moduli witness proved equal to the fixed field of its geometric-`j`
automorphism stabilizer inside the selected `Fbar`, the maximal solvable
extension inside that same `Fbar` obtained as the compositum of finite
solvable Galois layers, the mod-`l` representation and
kernel field, selected valuations, and valuation-derived q-parameter orders.
The finite and infinite place projections are canonical restrictions along
`Fmod -> K`; only their section is chosen. For a selected bad `K`-place, the
reduction and q-order APIs canonically contract it to its `F`-place and reuse
the Definition 3.1(b)-(c) data there. Clause (e) and the aggregate contain no
second independently chosen selected-place reduction or q-parameter family.
The aggregate contains source-shaped type-`(1,l-torsion)` and global plus
bad-local theta-root stack realizations. Their coherent sign quotients have the full
bicategorical quotient property, their cover squares have the full
two-pullback property, their arithmetic groups are tied to the derived open
subgroups, and both cover types carry the X-to-C-to-base open
fundamental-group chain. Constructing these realizations as finite-etale covers from
the source hypotheses remains open. In particular, the
class-two arithmetic theta quotient and its rank-two elliptic quotient are
distinct, and the Lagrangian quotient is attached to the latter, not directly
to the original arithmetic fundamental group. Proposition 2.2's inversion
decomposition acts on that rank-two quotient, with its conjugation
compatibility stated against actual arithmetic conjugation. These data are
attached only after the curve and `X_F/C_F` stacks have been scalar-extended
to `K`.
Every finite place of `K` carries curve and `X_v/C_v` scalar extensions
over the actual adic completion, identifies its absolute Galois group with a
closed decomposition subgroup of the global group, and carries compatible
embeddings of the two fundamental exact sequences. The type-`(1,l-torsion)`
cover itself is now scalar-extended at every selected place, with compatible
cover fundamental groups and rank-two elliptic quotients. Every selected infinite
place specializes analogous core data supplied at every infinite `K`-place
over mathlib's actual archimedean completion.
In both cases the decomposition subgroup is constrained to be the literal
stabilizer of a chosen prolongation of the place to `Kbar`.
The global-to-`K` and all local quotient maps satisfy the morphism-level
scalar-extension comparison. Theta-root stack models remain open.
The cusp data is now a complete atlas: nonzero `X`-cusps are indexed by actual
nonidentity `Q`-labels and `C`-cusps by their inversion orbits. Each entry
contains an actual point on a compactification, a representably open embedding
of the orbicurve, and a proof that the point lies outside the open image. A
closed decomposition subgroup then derives its profinite decomposition group,
inertia kernel, exact sequence, and ambient embedding. Sheet conjugacy,
`X -> C`, and inversion compatibility use those derived groups. The selected
label is derived from an actual sheet representative.

The transitive IUT I, Definition 1.1 construction is explicit. Lean forms the
normal closure of all nonselected cusp inertia, the quotient `Delta dagger`,
its positive/negative eigenspaces, and the doubled label `2 epsilon`; it proves
that the doubled label is nonzero and differs from both selected sheets. The
continuous `J_X` and `J_C` exact sequences and their inclusion are recorded,
the section is pinned to the doubled-cusp decomposition group, and Lean proves
its image normal from exactness and the trivial kernel action. The arrowed
stacks are required to realize the preimages of `Im(sigma)` and
`Im(sigma) x Gal(X/C)`, rather than unrelated cyclic quotients.

Complete cusp atlases localize at every selected finite and infinite place.
At good finite places the dagger quotient, positive profinite quotient,
`J_X/J_C`, doubled-cusp sections, arrowed stacks, and fundamental-group
diagrams all commute with scalar extension. Lean also proves that localization
preserves the selected global sign label.
At bad places, the rank-one quotient is now required to factor through
the actual profinite completion of `Z` and its canonical continuous reduction
modulo `l`; the cuspidal involution fixes inertia and the Galois quotient, the
selected splitting is sign-compatible, and the localized cusp label is proved
to be the sign orbit of the canonical class `1 mod l`. Constructing the
algebraic boundary atlas, compactifications, and finite-etale stack
realizations canonically from the initial curve hypotheses remains open; the
records now require those actual geometric objects and properties as
source-shaped existence obligations rather than accepting group-only labels.

`Stage1HodgeTheaterSource.ofInitialThetaData` derives typed `0`/`1` histories,
owned prime strips, the `Theta` plus-minus, ell, and NF bridge boundaries, and
their gluing. `IUTStage1InitialThetaPrimitiveSourcePacket` retains that typed
source and generates the old Stage 1 identifiers and history strings only
through explicit legacy projections.

The former `IUTIHodgeTheaterRealization` claim is now explicitly isolated as
`ToyIUTIHodgeTheaterRealization`. It is only a degree-preorder test double and
does not discharge IUT I, Definition 3.6, Corollary 3.7, Definitions 4.1 and
5.2, Proposition 6.7, Remark 6.12.2, or Definition 6.13. The source path starts
instead with the elementary category and full Definition 1.3 contract in
`Iut.Foundations.Frobenioid`. The obligation-only theater interface in
`Iut.Foundations.SourceThetaHodgeTheater` indexes the nonarchimedean,
archimedean, and global models by the actual selected places of
`SourceInitialThetaCore`; it deliberately has no constructor from initial
theta data. Frobenioids I Definition 2.7 pre-model type now includes its
standing all-objects-isotropic condition as well as a base--Frobenius pair.
The concrete model proof reuses its existing pointwise isotropic theorem, and
the generic API proves that a pair alone cannot overcome a non-isotropic
object. Given such a model package,
`Iut.Foundations.SourcePrimeStripConstructions` now constructs the canonical
`D`, `D~`, `F`, `F~`, and globally realified `F~` strips without accepting
additional component transports. The associated finite `D` constituent is
related to the named model `D_v` by the Frobenioid base-category equivalence;
the infinite constituent agrees definitionally. Mono-analytic strips form
the Section 0 quotient category of complete structured equivalences and have
genuine finite capsules. Generic procession arrows now retain the proposition
that each complete capsule-full member set is inhabited, without choosing a
member. This is exactly the condition under which Lean proves that composition
is the paper's multiplicity-free set of pairwise composites; a discrete
two-object regression also records the failure for empty intermediate member
sets. Constructing the model package, mono-analyticization,
the remaining finite/archimedean reconstruction algorithms, and the NF/theta
bridges are tracked separately by issues #34--#37. Given two theaters over
common cited models,
`SourceThetaLinkCore.ofTheaters` constructs the global theta-to-moduli
equivalence, the finite-place mono-analytic `D` transports, and the
finite/infinite topological unit-monoid transports. Packaging these maps as the
source's full poly-isomorphism remains open.

## Reproduce

```bash
lake build
lake env lean Iut/Stage1/IUTStage1StepXIDependencyAudit.lean
lake exe checkdecls blueprint/lean_decls
pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory=paper paper/IUT_FORMALIZATION_3_12_DRAFT.tex
```
