# M2: Hodge-Arakelov Evaluation and Concrete Pilots

> **Status correction (2026-07-20).** This document describes the legacy
> numerical pilot model, not completion of IUT II Hodge-Arakelov evaluation.
> See `Iut/SourceTrace/M1M3PaperLedger.lean` for clause-level status.

M2 extends the typed M1 boundary documented in
`docs/m1-typed-hodge-theater-source.md`; the reproducible M0 baseline remains
commit `6852a45a`.

## Boundary

The finite model constructs:

- effective-divisor degree preorder categories for the local, theta,
  plus-minus, and NF Frobenioid roles, with typed theta-link and gluing
  equivalences;
- a positive q-order pilot on the zero column, prime to `l`;
- a Gaussian `q^(j^2)` theta pilot on the one column at every bad place;
- coordinates from the actual theta-root quotient torsor, `ZMod l` labels,
  sign classes, balanced-square weights, and coordinate, weighted, and
  sign-orbit averages;
- positivity, zero/one normalization, sign invariance, translation invariance,
  and history-separation proofs.

`IUTStage1InitialThetaPrimitiveSourcePacket.ofInitialThetaData` consumes this
canonical M2 data. Old string and identifier fields remain only as explicit
legacy projections.

These calculations validate square-weight bookkeeping only. They do not
construct the evaluation morphisms, Gaussian monoids/Frobenioids, Kummer maps,
splittings, value profiles, or conjugate synchronization cited from IUT II and
therefore do not discharge M2.

## Reproduce

```bash
lake build
lake env lean Iut/Stage1/IUTStage1StepXIDependencyAudit.lean
lake exe checkdecls blueprint/lean_decls
pdflatex -interaction=nonstopmode -halt-on-error \
  -output-directory=paper paper/IUT_FORMALIZATION_3_12_DRAFT.tex
```
